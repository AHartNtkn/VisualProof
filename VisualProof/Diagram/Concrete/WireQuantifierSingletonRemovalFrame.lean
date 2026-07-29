import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemovalInnerFrame

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace SingletonRemovalSemantics

private abbrev Target
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :=
  ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate source removed

private theorem removed_mem_nodesAt
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :
    removed ∈
      source.val.nodesAt (source.val.nodes removed).region := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
  apply List.mem_filter.mpr
  exact ⟨Data.Finite.mem_allFin removed, by simp⟩

private theorem climb_add
    (diagram : ConcreteDiagram definitionCount)
    (first second : Nat)
    (region : diagram.RegionId) :
    diagram.climb (first + second) region =
      (diagram.climb first region).bind (diagram.climb second) := by
  induction first generalizing region with
  | zero => simp
  | succ first induction =>
      cases regionData : diagram.regions region with
      | sheet =>
          simp [Nat.succ_add, ConcreteDiagram.climb, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, regionData, Nat.succ_add] using
            induction parent

private theorem climb_succ_root_none
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (steps : Nat) :
    diagram.climb (steps + 1) diagram.root = none := by
  have rootData : diagram.regions diagram.root = .sheet :=
    wellFormed.root_is_sheet
  simp [ConcreteDiagram.climb, rootData]

private theorem climb_to_root_unique
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {left right : Nat}
    (leftClimb : diagram.climb left region = some diagram.root)
    (rightClimb : diagram.climb right region = some diagram.root) :
    left = right := by
  induction left generalizing right region with
  | zero =>
      have regionRoot : region = diagram.root := by
        simpa [ConcreteDiagram.climb] using leftClimb
      subst region
      cases right with
      | zero => rfl
      | succ right =>
          rw [climb_succ_root_none definitions diagram wellFormed right]
            at rightClimb
          contradiction
  | succ left induction =>
      cases right with
      | zero =>
          have regionRoot : region = diagram.root := by
            simpa [ConcreteDiagram.climb] using rightClimb
          subst region
          rw [climb_succ_root_none definitions diagram wellFormed left]
            at leftClimb
          contradiction
      | succ right =>
          cases regionData : diagram.regions region with
          | sheet =>
              simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              apply congrArg Nat.succ
              apply induction
              · simpa [ConcreteDiagram.climb, regionData] using leftClimb
              · simpa [ConcreteDiagram.climb, regionData] using rightClimb

private theorem checked_reaches_root
    (source : CheckedDiagram definitions)
    (region : source.val.RegionId) :
    ∃ steps : Fin (source.val.regionCount + 1),
      source.val.climb steps region = some source.val.root := by
  have checked :=
    (List.all_eq_true.mp source.property.all_regions_reach_root)
      region (Data.Finite.mem_allFin region)
  exact
    (ConcreteElaboration.encloses_iff_exists
      source.val source.val.root region).mp (of_decide_eq_true checked)

private theorem checked_encloses_trans
    (source : CheckedDiagram definitions)
    {outer middle inner : source.val.RegionId}
    (outerMiddle : source.val.Encloses outer middle)
    (middleInner : source.val.Encloses middle inner) :
    source.val.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val outer middle).mp outerMiddle
  obtain ⟨middleSteps, middleClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val middle inner).mp middleInner
  obtain ⟨rootSteps, outerRoot⟩ := checked_reaches_root source outer
  have composed :
      source.val.climb (middleSteps.val + outerSteps.val) inner =
        some outer := by
    rw [climb_add source.val middleSteps.val outerSteps.val inner,
      middleClimb]
    exact outerClimb
  have composedRoot :
      source.val.climb
          ((middleSteps.val + outerSteps.val) + rootSteps.val)
          inner =
        some source.val.root := by
    rw [climb_add source.val
      (middleSteps.val + outerSteps.val) rootSteps.val inner,
      composed]
    exact outerRoot
  obtain ⟨canonicalRootSteps, canonicalRoot⟩ :=
    checked_reaches_root source inner
  have sameDepth :=
    climb_to_root_unique definitions source.val source.property
      composedRoot canonicalRoot
  have composedBound :
      middleSteps.val + outerSteps.val < source.val.regionCount + 1 := by
    omega
  exact
    (ConcreteElaboration.encloses_iff_exists source.val outer inner).mpr
      ⟨⟨middleSteps.val + outerSteps.val, composedBound⟩, composed⟩

private theorem parent_encloses_child
    (diagram : ConcreteDiagram definitionCount)
    (child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent) :
    diagram.Encloses parent child := by
  apply
    (ConcreteElaboration.encloses_iff_exists
      diagram parent child).mpr
  refine ⟨⟨1, by have := child.isLt; omega⟩, ?_⟩
  simp [ConcreteDiagram.climb, childData]

private theorem child_outside
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region child : source.val.RegionId)
    (outside :
      ¬source.val.Encloses region (source.val.nodes removed).region)
    (member : child ∈ source.val.childrenOf region) :
    ¬source.val.Encloses child (source.val.nodes removed).region := by
  intro childSite
  have childData :=
    ConcreteElaboration.mem_childrenOf source.val region child member
  exact outside
    (checked_encloses_trans source
      (parent_encloses_child source.val child region childData)
      childSite)

private theorem child_outside_parent
    (source : CheckedDiagram definitions)
    (region child : source.val.RegionId)
    (member : child ∈ source.val.childrenOf region) :
    ¬source.val.Encloses child region := by
  intro childRegion
  have childData :=
    ConcreteElaboration.mem_childrenOf source.val region child member
  obtain ⟨backSteps, backClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val child region).mp childRegion
  obtain ⟨rootSteps, rootClimb⟩ := checked_reaches_root source child
  have cycle :
      source.val.climb (1 + backSteps.val) child = some child := by
    rw [climb_add source.val 1 backSteps.val child]
    simp [ConcreteDiagram.climb, childData, backClimb]
  have longRoot :
      source.val.climb ((1 + backSteps.val) + rootSteps.val) child =
        some source.val.root := by
    rw [climb_add source.val (1 + backSteps.val) rootSteps.val child,
      cycle]
    exact rootClimb
  have sameLength :=
    climb_to_root_unique definitions source.val source.property
      longRoot rootClimb
  omega

theorem enclosing_children_unique
    (source : CheckedDiagram definitions)
    (region left right site : source.val.RegionId)
    (leftMember : left ∈ source.val.childrenOf region)
    (rightMember : right ∈ source.val.childrenOf region)
    (leftSite : source.val.Encloses left site)
    (rightSite : source.val.Encloses right site) :
    left = right := by
  have leftData :=
    ConcreteElaboration.mem_childrenOf source.val region left leftMember
  have rightData :=
    ConcreteElaboration.mem_childrenOf source.val region right rightMember
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val left site).mp leftSite
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      source.val right site).mp rightSite
  obtain ⟨rootSteps, rootClimb⟩ := checked_reaches_root source region
  have leftRegion :
      source.val.climb (leftSteps.val + 1) site = some region := by
    rw [climb_add source.val leftSteps.val 1 site, leftClimb]
    simp [ConcreteDiagram.climb, leftData]
  have rightRegion :
      source.val.climb (rightSteps.val + 1) site = some region := by
    rw [climb_add source.val rightSteps.val 1 site, rightClimb]
    simp [ConcreteDiagram.climb, rightData]
  have leftRoot :
      source.val.climb
          ((leftSteps.val + 1) + rootSteps.val) site =
        some source.val.root := by
    rw [climb_add source.val (leftSteps.val + 1) rootSteps.val site,
      leftRegion]
    exact rootClimb
  have rightRoot :
      source.val.climb
          ((rightSteps.val + 1) + rootSteps.val) site =
        some source.val.root := by
    rw [climb_add source.val (rightSteps.val + 1) rootSteps.val site,
      rightRegion]
    exact rootClimb
  have sameLength :=
    climb_to_root_unique definitions source.val source.property
      leftRoot rightRoot
  have stepsExact : leftSteps.val = rightSteps.val := by omega
  rw [stepsExact] at leftClimb
  exact Option.some.inj (leftClimb.symm.trans rightClimb)

private theorem removed_not_mem_nodesAt
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId)
    (outside :
      ¬source.val.Encloses region (source.val.nodes removed).region) :
    removed ∉ source.val.nodesAt region := by
  intro member
  have owner : (source.val.nodes removed).region = region := by
    unfold ConcreteDiagram.nodesAt at member
    exact eq_of_beq (List.mem_filter.mp member).2
  apply outside
  rw [owner]
  exact ConcreteDiagram.encloses_refl source.val region

theorem removed_not_mem_nodesAt_of_ne
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId)
    (different : region ≠ (source.val.nodes removed).region) :
    removed ∉ source.val.nodesAt region := by
  intro member
  have owner : (source.val.nodes removed).region = region := by
    unfold ConcreteDiagram.nodesAt at member
    exact eq_of_beq (List.mem_filter.mp member).2
  exact different owner.symm

theorem compileNodes_cast_context
    (diagram : ConcreteDiagram definitions.length)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (nodes : List diagram.NodeId)
    {items : ItemSeq definitions left.sigs}
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram left nodes =
        some items) :
    ConcreteElaboration.compileNodes? definitions diagram right nodes =
      some
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ items) := by
  subst right
  exact compiled

private theorem compileChildren_cast_context
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
        Option (Region definitions context.sigs))
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (children : List diagram.RegionId)
    {items : ItemSeq definitions left.sigs}
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          left children =
        some items) :
    ConcreteElaboration.compileChildrenWith? definitions diagram recurse
        right children =
      some
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ items) := by
  subst right
  exact compiled

private theorem compileRegion_cast_context
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (region : diagram.RegionId)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    {body : Region definitions left.sigs}
    (compiled :
      ConcreteElaboration.compileRegion? definitions diagram fuel region left =
        some body) :
    ConcreteElaboration.compileRegion? definitions diagram fuel region right =
      some (congrArg ConcreteElaboration.WireContext.sigs same ▸ body) := by
  subst right
  exact compiled

private theorem denoteItemSeq_equiv_cast_target
    {sourceSigs targetCanonical targetActual : List Sig}
    (same : targetCanonical = targetActual)
    (rho : WireRenaming sourceSigs targetCanonical)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceItems : ItemSeq definitions sourceSigs)
    (targetItems : ItemSeq definitions targetActual)
    (targetEnv : Env pre targetActual)
    (canonical :
      denoteItemSeq pre definitionEnv (same.symm ▸ targetEnv)
          (same.symm ▸ targetItems) ↔
        denoteItemSeq pre definitionEnv
          (Env.comp (same.symm ▸ targetEnv) rho) sourceItems) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv (same ▸ rho)) sourceItems := by
  subst targetActual
  exact canonical

private theorem erasedItemSeq_equiv_cast_target
    {sourceSigs targetCanonical targetActual : List Sig}
    (same : targetCanonical = targetActual)
    (rho : WireRenaming sourceSigs targetCanonical)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceItems : ItemSeq definitions sourceSigs)
    (removedItem : Item definitions sourceSigs)
    (targetItems : ItemSeq definitions targetActual)
    (targetEnv : Env pre targetActual)
    (canonical :
      denoteItemSeq pre definitionEnv
          (Env.comp (same.symm ▸ targetEnv) rho) sourceItems ↔
        denoteItem pre definitionEnv
            (Env.comp (same.symm ▸ targetEnv) rho) removedItem ∧
          denoteItemSeq pre definitionEnv (same.symm ▸ targetEnv)
            (same.symm ▸ targetItems)) :
    denoteItemSeq pre definitionEnv
        (Env.comp targetEnv (same ▸ rho)) sourceItems ↔
      denoteItem pre definitionEnv
          (Env.comp targetEnv (same ▸ rho)) removedItem ∧
        denoteItemSeq pre definitionEnv targetEnv targetItems := by
  subst targetActual
  exact canonical

private theorem denoteRegion_equiv_cast_target
    {sourceSigs targetCanonical targetActual : List Sig}
    (same : targetCanonical = targetActual)
    (rho : WireRenaming sourceSigs targetCanonical)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (sourceBody : Region definitions sourceSigs)
    (targetBody : Region definitions targetActual)
    (targetEnv : Env pre targetActual)
    (canonical :
      denoteRegion pre definitionEnv (same.symm ▸ targetEnv)
          (same.symm ▸ targetBody) ↔
        denoteRegion pre definitionEnv
          (Env.comp (same.symm ▸ targetEnv) rho) sourceBody) :
    denoteRegion pre definitionEnv targetEnv targetBody ↔
      denoteRegion pre definitionEnv
        (Env.comp targetEnv (same ▸ rho)) sourceBody := by
  subst targetActual
  exact canonical

theorem LocalReplacementAt.cast
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    {sourceLeft sourceRight :
      ConcreteElaboration.WireContext source.val}
    {targetLeft targetRight :
      ConcreteElaboration.WireContext (Target source removed)}
    (sourceSame : sourceLeft = sourceRight)
    (targetSame : targetLeft = targetRight)
    (leftExact :
      targetLeft = targetContext source removed sourceLeft)
    (rightExact :
      targetRight = targetContext source removed sourceRight)
    (replacement : Region definitions targetLeft.sigs)
    (removedItem : Item definitions sourceLeft.sigs)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetRight.sigs)
    (equivalent :
      LocalReplacementAt source removed sourceLeft targetLeft leftExact
        replacement removedItem pre definitionEnv
        (congrArg ConcreteElaboration.WireContext.sigs targetSame.symm ▸
          targetEnv)) :
    LocalReplacementAt source removed sourceRight targetRight rightExact
      (congrArg ConcreteElaboration.WireContext.sigs targetSame ▸ replacement)
      (congrArg ConcreteElaboration.WireContext.sigs sourceSame ▸ removedItem)
      pre definitionEnv targetEnv := by
  subst sourceRight
  subst targetRight
  have exactProof : rightExact = leftExact := Subsingleton.elim _ _
  subst rightExact
  exact equivalent

theorem env_comp_cast_renaming
    {sourceSigs targetCanonical targetActual : List Sig}
    (same : targetCanonical = targetActual)
    (rho : WireRenaming sourceSigs targetCanonical)
    (pre : PreModel)
    (targetEnv : Env pre targetActual) :
    Env.comp targetEnv (same ▸ rho) =
      Env.comp (same.symm ▸ targetEnv) rho := by
  subst targetActual
  rfl

theorem cast_itemSeq_singleton
    {left right : List Sig}
    (same : left = right)
    (item : Item definitions left) :
    same ▸ (.cons item .nil : ItemSeq definitions left) =
      (.cons (same ▸ item) .nil : ItemSeq definitions right) := by
  subst right
  rfl

private theorem denote_compileChildren_iff_regions
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
        Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs)
    (children : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context children =
        some items) :
    denoteItemSeq pre definitionEnv env items ↔
      ∀ child, child ∈ children →
        ∃ body,
          recurse child context = some body ∧
            ¬denoteRegion pre definitionEnv env body := by
  induction children generalizing items with
  | nil =>
      simp only [ConcreteElaboration.compileChildrenWith?] at compiled
      have empty : items = .nil := Option.some.inj compiled.symm
      subst items
      simp
  | cons child tail induction =>
      obtain ⟨body, rest, bodyCompiled, restCompiled, itemsEquation⟩ :=
        InsertionCompilation.NaturalityInternal.compileChildren_cons_components
          definitions diagram recurse context child tail items compiled
      subst items
      rw [denoteItemSeq_cons, cut_denotes_negation,
        induction rest restCompiled]
      constructor
      · rintro ⟨bodyNot, tailEach⟩ candidate member
        rcases List.mem_cons.mp member with same | tailMember
        · subst candidate
          exact ⟨body, bodyCompiled, bodyNot⟩
        · exact tailEach candidate tailMember
      · intro each
        obtain ⟨actual, actualCompiled, actualNot⟩ :=
          each child (by simp)
        have same : actual = body :=
          Option.some.inj (actualCompiled.symm.trans bodyCompiled)
        subst actual
        exact
          ⟨actualNot, fun candidate tailMember =>
            each candidate (List.mem_cons_of_mem child tailMember)⟩

private theorem compileChild_of_member
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : ConcreteElaboration.WireContext diagram) →
        Option (Region definitions context.sigs))
    (context : ConcreteElaboration.WireContext diagram)
    (children : List diagram.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileChildrenWith? definitions diagram recurse
          context children =
        some items)
    (child : diagram.RegionId)
    (member : child ∈ children) :
    ∃ body, recurse child context = some body := by
  induction children generalizing items with
  | nil => simp at member
  | cons head tail induction =>
      obtain ⟨body, rest, bodyCompiled, restCompiled, _⟩ :=
        InsertionCompilation.NaturalityInternal.compileChildren_cons_components
          definitions diagram recurse context head tail items compiled
      rcases List.mem_cons.mp member with same | tailMember
      · subst child
        exact ⟨body, bodyCompiled⟩
      · exact induction rest restCompiled tailMember

theorem compiledNodes_outside
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    (context : ConcreteElaboration.WireContext source.val)
    (contextNodup : context.ids.Nodup)
    (region : source.val.RegionId)
    (removedOutside : removed ∉ source.val.nodesAt region)
    {sourceItems : ItemSeq definitions context.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          (source.val.nodesAt region) =
        some sourceItems)
    {targetItems :
      ItemSeq definitions (targetContext source removed context).sigs}
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions (Target source removed)
          (targetContext source removed context)
          ((Target source removed).nodesAt
            (targetRegion source removed region)) =
        some targetItems)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre (targetContext source removed context).sigs) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv (contextRenaming source removed context))
        sourceItems := by
  have filtered :
      (source.val.nodesAt region).filter
          (fun node => decide (node ≠ removed)) =
        source.val.nodesAt region := by
    apply List.filter_eq_self.mpr
    intro node member
    simp only [decide_eq_true_eq]
    exact fun same => removedOutside (same ▸ member)
  have sourceTargets :
      ConcreteElaboration.compileNodes? definitions source.val context
          (((Target source removed).nodesAt
            (targetRegion source removed region)).map
              (sourceNode source removed)) =
        some sourceItems := by
    simp only [targetRegion]
    rw [erased_nodesAt_sources, filtered]
    exact sourceCompiled
  obtain ⟨expected, expectedCompiled, equivalent⟩ :=
    survivingNodes_denotation source removed candidateWellFormed context
      contextNodup
      ((Target source removed).nodesAt
        (targetRegion source removed region))
      sourceTargets pre definitionEnv targetEnv
  have same : targetItems = expected :=
    Option.some.inj (targetCompiled.symm.trans expectedCompiled)
  subst targetItems
  exact equivalent

theorem compiledNodes_outside_extended
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (contextNodup : (context.extend region).ids.Nodup)
    (removedOutside : removed ∉ source.val.nodesAt region)
    {sourceItems : ItemSeq definitions (context.extend region).sigs}
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) (source.val.nodesAt region) =
        some sourceItems)
    {targetItems :
      ItemSeq definitions
        ((targetContext source removed context).extend
          (targetRegion source removed region)).sigs}
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions (Target source removed)
          ((targetContext source removed context).extend
            (targetRegion source removed region))
          ((Target source removed).nodesAt
            (targetRegion source removed region)) =
        some targetItems)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre
        ((targetContext source removed context).extend
          (targetRegion source removed region)).sigs) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv
          (extendedContextRenaming source removed context region))
        sourceItems := by
  let same := targetContext_extend source removed context region
  let canonicalItems :
      ItemSeq definitions
        (targetContext source removed (context.extend region)).sigs :=
    congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ targetItems
  let canonicalEnv :
      Env pre (targetContext source removed (context.extend region)).sigs :=
    congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ targetEnv
  have canonicalCompiled :
      ConcreteElaboration.compileNodes? definitions (Target source removed)
          (targetContext source removed (context.extend region))
          ((Target source removed).nodesAt
            (targetRegion source removed region)) =
        some canonicalItems :=
    compileNodes_cast_context (Target source removed) same.symm _ targetCompiled
  have canonical :=
    compiledNodes_outside source removed candidateWellFormed
      (context.extend region) contextNodup region removedOutside
      sourceCompiled canonicalCompiled pre definitionEnv canonicalEnv
  exact
    denoteItemSeq_equiv_cast_target
      (congrArg ConcreteElaboration.WireContext.sigs same)
      (contextRenaming source removed (context.extend region))
      pre definitionEnv sourceItems targetItems targetEnv
      (by simpa [canonicalItems, canonicalEnv] using canonical)

theorem erasedNodes_denotation_extended
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (contextNodup : (context.extend region).ids.Nodup)
    (removedMember : removed ∈ source.val.nodesAt region)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre
        ((targetContext source removed context).extend
          (targetRegion source removed region)).sigs)
    (sourceItems : ItemSeq definitions (context.extend region).sigs)
    (sourceCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) (source.val.nodesAt region) =
        some sourceItems)
    (targetItems :
      ItemSeq definitions
        ((targetContext source removed context).extend
          (targetRegion source removed region)).sigs)
    (targetCompiled :
      ConcreteElaboration.compileNodes? definitions (Target source removed)
          ((targetContext source removed context).extend
            (targetRegion source removed region))
          ((Target source removed).nodesAt
            (targetRegion source removed region)) =
        some targetItems)
    (removedItem : Item definitions (context.extend region).sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (context.extend region) [removed] =
        some (.cons removedItem .nil)) :
    denoteItemSeq pre definitionEnv
        (Env.comp targetEnv
          (extendedContextRenaming source removed context region))
        sourceItems ↔
      denoteItem pre definitionEnv
          (Env.comp targetEnv
            (extendedContextRenaming source removed context region))
          removedItem ∧
        denoteItemSeq pre definitionEnv targetEnv targetItems := by
  let same := targetContext_extend source removed context region
  let canonicalItems :
      ItemSeq definitions
        (targetContext source removed (context.extend region)).sigs :=
    congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ targetItems
  let canonicalEnv :
      Env pre (targetContext source removed (context.extend region)).sigs :=
    congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ targetEnv
  have canonicalCompiled :
      ConcreteElaboration.compileNodes? definitions (Target source removed)
          (targetContext source removed (context.extend region))
          ((Target source removed).nodesAt
            (targetRegion source removed region)) =
        some canonicalItems :=
    compileNodes_cast_context (Target source removed) same.symm _
      targetCompiled
  have canonical :=
    erasedNodes_denotation source removed candidateWellFormed
      (context.extend region) contextNodup region removedMember pre
      definitionEnv canonicalEnv sourceItems sourceCompiled canonicalItems
      canonicalCompiled removedItem removedCompiled
  exact
    erasedItemSeq_equiv_cast_target
      (congrArg ConcreteElaboration.WireContext.sigs same)
      (contextRenaming source removed (context.extend region))
      pre definitionEnv sourceItems removedItem targetItems targetEnv
      (by simpa [canonicalItems, canonicalEnv] using canonical)

theorem compiledChildren_equiv
    (sourceDiagram : ConcreteDiagram definitions.length)
    (targetDiagram : ConcreteDiagram definitions.length)
    (sourceRecurse : (region : sourceDiagram.RegionId) →
      (context : ConcreteElaboration.WireContext sourceDiagram) →
        Option (Region definitions context.sigs))
    (targetRecurse : (region : targetDiagram.RegionId) →
      (context : ConcreteElaboration.WireContext targetDiagram) →
        Option (Region definitions context.sigs))
    (sourceContext : ConcreteElaboration.WireContext sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext targetDiagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (mapRegion : sourceDiagram.RegionId → targetDiagram.RegionId)
    (children : List sourceDiagram.RegionId)
    {sourceItems : ItemSeq definitions sourceContext.sigs}
    (sourceCompiled :
      ConcreteElaboration.compileChildrenWith? definitions sourceDiagram
          sourceRecurse sourceContext children =
        some sourceItems)
    {targetItems : ItemSeq definitions targetContext.sigs}
    (targetCompiled :
      ConcreteElaboration.compileChildrenWith? definitions targetDiagram
          targetRecurse targetContext (children.map mapRegion) =
        some targetItems)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv : Env pre targetContext.sigs)
    (each :
      ∀ child, child ∈ children →
        ∀ sourceBody targetBody,
          sourceRecurse child sourceContext = some sourceBody →
          targetRecurse (mapRegion child) targetContext = some targetBody →
          (denoteRegion pre definitionEnv targetEnv targetBody ↔
            denoteRegion pre definitionEnv
              (Env.comp targetEnv rho) sourceBody)) :
    denoteItemSeq pre definitionEnv targetEnv targetItems ↔
      denoteItemSeq pre definitionEnv
        (Env.comp targetEnv rho) sourceItems := by
  rw [denote_compileChildren_iff_regions definitions targetDiagram
      targetRecurse targetContext pre definitionEnv targetEnv
      _ _ targetCompiled,
    denote_compileChildren_iff_regions definitions sourceDiagram
      sourceRecurse sourceContext pre definitionEnv
      (Env.comp targetEnv rho) _ _ sourceCompiled]
  constructor
  · intro targetEach child member
    obtain ⟨sourceBody, sourceBodyCompiled⟩ :=
      compileChild_of_member definitions sourceDiagram sourceRecurse
        sourceContext children sourceItems sourceCompiled child member
    obtain ⟨targetBody, targetBodyCompiled, targetNot⟩ :=
      targetEach (mapRegion child) (List.mem_map.mpr ⟨child, member, rfl⟩)
    exact
      ⟨sourceBody, sourceBodyCompiled,
        fun sourceHolds =>
          targetNot ((each child member sourceBody targetBody
            sourceBodyCompiled targetBodyCompiled).mpr sourceHolds)⟩
  · intro sourceEach targetChild targetMember
    obtain ⟨child, member, targetExact⟩ :=
      List.mem_map.mp targetMember
    subst targetChild
    obtain ⟨targetBody, targetBodyCompiled⟩ :=
      compileChild_of_member definitions targetDiagram targetRecurse
        targetContext (children.map mapRegion) targetItems targetCompiled
        (mapRegion child) (List.mem_map.mpr ⟨child, member, rfl⟩)
    obtain ⟨sourceBody, sourceBodyCompiled, sourceNot⟩ :=
      sourceEach child member
    exact
      ⟨targetBody, targetBodyCompiled,
        fun targetHolds =>
          sourceNot ((each child member sourceBody targetBody
            sourceBodyCompiled targetBodyCompiled).mp targetHolds)⟩

set_option maxHeartbeats 1200000 in
theorem compileRegion_equiv_outside
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed : (Target source removed).WellFormed definitions) :
    ∀ (fuel : Nat)
      (sourceContext : ConcreteElaboration.WireContext source.val)
      (region : source.val.RegionId)
      (sourceAbove :
        ConcreteElaboration.ContextAbove source.val sourceContext region)
      (outside :
        ¬source.val.Encloses region (source.val.nodes removed).region)
      {sourceBody : Region definitions sourceContext.sigs}
      {targetBody :
        Region definitions (targetContext source removed sourceContext).sigs},
      ConcreteElaboration.compileRegion? definitions source.val fuel region
          sourceContext =
        some sourceBody →
      ConcreteElaboration.compileRegion? definitions (Target source removed)
          fuel (targetRegion source removed region)
          (targetContext source removed sourceContext) =
        some targetBody →
      ∀ (pre : PreModel) (definitionEnv : DefinitionEnv pre definitions)
        (targetEnv :
          Env pre (targetContext source removed sourceContext).sigs),
        denoteRegion pre definitionEnv targetEnv targetBody ↔
          denoteRegion pre definitionEnv
            (Env.comp targetEnv
              (contextRenaming source removed sourceContext))
            sourceBody := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceContext region sourceAbove outside sourceBody targetBody
        sourceCompiled
      simp [ConcreteElaboration.compileRegion?] at sourceCompiled
  | succ childFuel induction =>
      intro sourceContext region sourceAbove outside sourceBody targetBody
        sourceCompiled targetCompiled pre definitionEnv targetEnv
      simp only [ConcreteElaboration.compileRegion?] at sourceCompiled targetCompiled
      obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
        Option.bind_eq_some_iff.mp sourceCompiled
      obtain ⟨sourceChildren, sourceChildrenCompiled, sourceBodyEquation⟩ :=
        Option.bind_eq_some_iff.mp sourceAfterNodes
      have sourceBodyExact :
          ConcreteElaboration.finishRegion source.val sourceContext region
              (.mk (sourceNodes.append sourceChildren)) =
            sourceBody :=
        Option.some.inj sourceBodyEquation
      subst sourceBody
      obtain ⟨targetNodes, targetNodesCompiled, targetAfterNodes⟩ :=
        Option.bind_eq_some_iff.mp targetCompiled
      obtain ⟨targetChildren, targetChildrenCompiled, targetBodyEquation⟩ :=
        Option.bind_eq_some_iff.mp targetAfterNodes
      have targetBodyExact :
          ConcreteElaboration.finishRegion (Target source removed)
              (targetContext source removed sourceContext)
              (targetRegion source removed region)
              (.mk (targetNodes.append targetChildren)) =
            targetBody :=
        Option.some.inj targetBodyEquation
      subst targetBody
      have sourceExtendedNodup :
          (sourceContext.extend region).ids.Nodup :=
        ConcreteElaboration.extend_nodup definitions source.val
          source.property sourceContext region sourceAbove
      have targetChildrenCompiled' :
          ConcreteElaboration.compileChildrenWith? definitions
              (Target source removed)
              (ConcreteElaboration.compileRegion? definitions
                (Target source removed) childFuel)
              ((targetContext source removed sourceContext).extend
                (targetRegion source removed region))
              ((source.val.childrenOf region).map
                (targetRegion source removed)) =
            some targetChildren := by
        rw [← target_childrenOf]
        exact targetChildrenCompiled
      have coreEquiv :
          ∀ currentTarget :
              Env pre
                ((targetContext source removed sourceContext).extend
                  (targetRegion source removed region)).sigs,
            denoteRegion pre definitionEnv currentTarget
                (.mk (targetNodes.append targetChildren)) ↔
              denoteRegion pre definitionEnv
                (Env.comp currentTarget
                  (extendedContextRenaming source removed sourceContext
                    region))
                (.mk (sourceNodes.append sourceChildren)) := by
        intro currentTarget
        have nodesEquiv :=
          compiledNodes_outside_extended source removed candidateWellFormed
            sourceContext region sourceExtendedNodup
            (removed_not_mem_nodesAt source removed region outside)
            sourceNodesCompiled targetNodesCompiled pre definitionEnv
            currentTarget
        have childrenEquiv :=
          compiledChildren_equiv source.val (Target source removed)
            (ConcreteElaboration.compileRegion? definitions source.val
              childFuel)
            (ConcreteElaboration.compileRegion? definitions
              (Target source removed) childFuel)
            (sourceContext.extend region)
            ((targetContext source removed sourceContext).extend
              (targetRegion source removed region))
            (extendedContextRenaming source removed sourceContext region)
            (targetRegion source removed) (source.val.childrenOf region)
            sourceChildrenCompiled targetChildrenCompiled' pre definitionEnv
            currentTarget
            (by
              intro child member sourceChild targetChild
                sourceChildCompiled targetChildCompiled
              have childData :=
                ConcreteElaboration.mem_childrenOf source.val region child
                  member
              have childAbove :=
                ConcreteElaboration.extend_above_child definitions source.val
                  source.property sourceContext region child sourceAbove
                  childData
              let same :=
                targetContext_extend source removed sourceContext region
              let canonicalTarget :
                  Region definitions
                    (targetContext source removed
                      (sourceContext.extend region)).sigs :=
                congrArg ConcreteElaboration.WireContext.sigs same.symm ▸
                  targetChild
              let canonicalEnv :
                  Env pre
                    (targetContext source removed
                      (sourceContext.extend region)).sigs :=
                congrArg ConcreteElaboration.WireContext.sigs same.symm ▸
                  currentTarget
              have canonicalCompiled :
                  ConcreteElaboration.compileRegion? definitions
                      (Target source removed) childFuel
                      (targetRegion source removed child)
                      (targetContext source removed
                        (sourceContext.extend region)) =
                    some canonicalTarget :=
                compileRegion_cast_context (Target source removed) childFuel
                  (targetRegion source removed child) same.symm
                  targetChildCompiled
              have recursive :=
                induction (sourceContext.extend region) child childAbove
                  (child_outside source removed region child outside member)
                  sourceChildCompiled canonicalCompiled pre definitionEnv
                  canonicalEnv
              exact
                denoteRegion_equiv_cast_target
                  (congrArg ConcreteElaboration.WireContext.sigs same)
                  (contextRenaming source removed
                    (sourceContext.extend region))
                  pre definitionEnv sourceChild targetChild currentTarget
                  (by
                    simpa [canonicalTarget, canonicalEnv] using recursive))
        simpa only [denoteRegion, denoteItemSeq_append] using
          and_congr nodesEquiv childrenEquiv
      rw [ConcreteElaboration.denote_finishRegion,
        ConcreteElaboration.denote_finishRegion]
      constructor
      · rintro ⟨targetValues, targetCore⟩
        obtain ⟨sourceValues, environments⟩ :=
          (extendedEnvironment_correspondence source removed sourceContext
            region sourceExtendedNodup pre
            (Env.comp targetEnv
              (contextRenaming source removed sourceContext))
            targetEnv rfl).2 targetValues
        refine ⟨sourceValues, ?_⟩
        rw [environments]
        exact (coreEquiv _).mp targetCore
      · rintro ⟨sourceValues, sourceCore⟩
        obtain ⟨targetValues, environments⟩ :=
          (extendedEnvironment_correspondence source removed sourceContext
            region sourceExtendedNodup pre
            (Env.comp targetEnv
              (contextRenaming source removed sourceContext))
            targetEnv rfl).1 sourceValues
        refine ⟨targetValues, ?_⟩
        apply (coreEquiv _).mpr
        rw [environments] at sourceCore
        exact sourceCore

theorem compileRegion_equiv_outside_extended
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    (fuel : Nat)
    (context : ConcreteElaboration.WireContext source.val)
    (region child : source.val.RegionId)
    (childAbove :
      ConcreteElaboration.ContextAbove source.val
        (context.extend region) child)
    (outside :
      ¬source.val.Encloses child (source.val.nodes removed).region)
    {sourceBody : Region definitions (context.extend region).sigs}
    (sourceCompiled :
      ConcreteElaboration.compileRegion? definitions source.val fuel child
          (context.extend region) =
        some sourceBody)
    {targetBody :
      Region definitions
        ((targetContext source removed context).extend
          (targetRegion source removed region)).sigs}
    (targetCompiled :
      ConcreteElaboration.compileRegion? definitions (Target source removed)
          fuel (targetRegion source removed child)
          ((targetContext source removed context).extend
            (targetRegion source removed region)) =
        some targetBody)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre
        ((targetContext source removed context).extend
          (targetRegion source removed region)).sigs) :
    denoteRegion pre definitionEnv targetEnv targetBody ↔
      denoteRegion pre definitionEnv
        (Env.comp targetEnv
          (extendedContextRenaming source removed context region))
        sourceBody := by
  let same := targetContext_extend source removed context region
  let canonicalBody :
      Region definitions
        (targetContext source removed (context.extend region)).sigs :=
    congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ targetBody
  let canonicalEnv :
      Env pre (targetContext source removed (context.extend region)).sigs :=
    congrArg ConcreteElaboration.WireContext.sigs same.symm ▸ targetEnv
  have canonicalCompiled :
      ConcreteElaboration.compileRegion? definitions (Target source removed)
          fuel (targetRegion source removed child)
          (targetContext source removed (context.extend region)) =
        some canonicalBody :=
    compileRegion_cast_context (Target source removed) fuel
      (targetRegion source removed child) same.symm targetCompiled
  have canonical :=
    compileRegion_equiv_outside source removed candidateWellFormed fuel
      (context.extend region) child childAbove outside sourceCompiled
      canonicalCompiled pre definitionEnv canonicalEnv
  exact
    denoteRegion_equiv_cast_target
      (congrArg ConcreteElaboration.WireContext.sigs same)
      (contextRenaming source removed (context.extend region))
      pre definitionEnv sourceBody targetBody targetEnv
      (by simpa [canonicalBody, canonicalEnv] using canonical)

theorem compileScopeBody_replacement
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceAbove :
      ConcreteElaboration.ContextAbove source.val sourceOuter
        (source.val.nodes removed).region)
    (sourceBody :
      Region definitions
        (sourceOuter.extend (source.val.nodes removed).region).sigs)
    (targetBody :
      Region definitions
        ((targetContext source removed sourceOuter).extend
          (targetRegion source removed
            (source.val.nodes removed).region)).sigs)
    (sourceCompiled :
      compileRegionBody? definitions source.val fuel
          (source.val.nodes removed).region sourceOuter =
        some sourceBody)
    (targetCompiled :
      compileRegionBody? definitions (Target source removed) fuel
          (targetRegion source removed
            (source.val.nodes removed).region)
          (targetContext source removed sourceOuter) =
        some targetBody)
    (replacement :
      Region definitions
        ((targetContext source removed sourceOuter).extend
          (targetRegion source removed
            (source.val.nodes removed).region)).sigs)
    (removedItem :
      Item definitions
        (sourceOuter.extend (source.val.nodes removed).region).sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          (sourceOuter.extend (source.val.nodes removed).region) [removed] =
        some (.cons removedItem .nil))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (targetEnv :
      Env pre
        ((targetContext source removed sourceOuter).extend
          (targetRegion source removed
            (source.val.nodes removed).region)).sigs)
    (localEquiv :
      denoteRegion pre definitionEnv targetEnv replacement ↔
        denoteItem pre definitionEnv
          (Env.comp targetEnv
            (extendedContextRenaming source removed sourceOuter
              (source.val.nodes removed).region))
          removedItem) :
    denoteRegion pre definitionEnv targetEnv
        (replacement.conjoin targetBody) ↔
      denoteRegion pre definitionEnv
        (Env.comp targetEnv
          (extendedContextRenaming source removed sourceOuter
            (source.val.nodes removed).region))
        sourceBody := by
  unfold compileRegionBody? at sourceCompiled targetCompiled
  obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
    Option.bind_eq_some_iff.mp sourceCompiled
  obtain ⟨sourceChildren, sourceChildrenCompiled, sourceBodyEquation⟩ :=
    Option.bind_eq_some_iff.mp sourceAfterNodes
  have sourceBodyExact :
      (.mk (sourceNodes.append sourceChildren) :
        Region definitions
          (sourceOuter.extend (source.val.nodes removed).region).sigs) =
        sourceBody :=
    Option.some.inj sourceBodyEquation
  subst sourceBody
  obtain ⟨targetNodes, targetNodesCompiled, targetAfterNodes⟩ :=
    Option.bind_eq_some_iff.mp targetCompiled
  obtain ⟨targetChildren, targetChildrenCompiled, targetBodyEquation⟩ :=
    Option.bind_eq_some_iff.mp targetAfterNodes
  have targetBodyExact :
      (.mk (targetNodes.append targetChildren) :
        Region definitions
          ((targetContext source removed sourceOuter).extend
            (targetRegion source removed
              (source.val.nodes removed).region)).sigs) =
        targetBody :=
    Option.some.inj targetBodyEquation
  subst targetBody
  have sourceExtendedNodup :
      (sourceOuter.extend
        (source.val.nodes removed).region).ids.Nodup :=
    ConcreteElaboration.extend_nodup definitions source.val
      source.property sourceOuter (source.val.nodes removed).region
      sourceAbove
  have targetChildrenCompiled' :
      ConcreteElaboration.compileChildrenWith? definitions
          (Target source removed)
          (ConcreteElaboration.compileRegion? definitions
            (Target source removed) fuel)
          ((targetContext source removed sourceOuter).extend
            (targetRegion source removed
              (source.val.nodes removed).region))
          ((source.val.childrenOf
            (source.val.nodes removed).region).map
              (targetRegion source removed)) =
        some targetChildren := by
    rw [← target_childrenOf]
    exact targetChildrenCompiled
  have childrenEquiv :
      denoteItemSeq pre definitionEnv targetEnv targetChildren ↔
        denoteItemSeq pre definitionEnv
          (Env.comp targetEnv
            (extendedContextRenaming source removed sourceOuter
              (source.val.nodes removed).region))
          sourceChildren :=
    compiledChildren_equiv source.val (Target source removed)
      (ConcreteElaboration.compileRegion? definitions source.val fuel)
      (ConcreteElaboration.compileRegion? definitions
        (Target source removed) fuel)
      (sourceOuter.extend (source.val.nodes removed).region)
      ((targetContext source removed sourceOuter).extend
        (targetRegion source removed
          (source.val.nodes removed).region))
      (extendedContextRenaming source removed sourceOuter
        (source.val.nodes removed).region)
      (targetRegion source removed)
      (source.val.childrenOf (source.val.nodes removed).region)
      sourceChildrenCompiled targetChildrenCompiled' pre definitionEnv
      targetEnv
      (by
        intro child member sourceChild targetChild sourceChildCompiled
          targetChildCompiled
        have childData :=
          ConcreteElaboration.mem_childrenOf source.val
            (source.val.nodes removed).region child member
        have childAbove :=
          ConcreteElaboration.extend_above_child definitions source.val
            source.property sourceOuter
            (source.val.nodes removed).region child sourceAbove childData
        exact
          compileRegion_equiv_outside_extended source removed
            candidateWellFormed fuel sourceOuter
            (source.val.nodes removed).region child childAbove
            (child_outside_parent source
              (source.val.nodes removed).region child member)
            sourceChildCompiled targetChildCompiled pre definitionEnv
            targetEnv)
  have nodesEquiv :=
    erasedNodes_denotation_extended source removed candidateWellFormed
      sourceOuter (source.val.nodes removed).region sourceExtendedNodup
      (removed_mem_nodesAt source removed) pre definitionEnv targetEnv
      sourceNodes sourceNodesCompiled targetNodes targetNodesCompiled
      removedItem removedCompiled
  rw [Region.denote_conjoin, denoteRegion, denoteItemSeq_append,
    denoteRegion, denoteItemSeq_append]
  constructor
  · rintro ⟨replacementHolds, targetNodesHold, targetChildrenHold⟩
    exact
      ⟨nodesEquiv.mpr
          ⟨localEquiv.mp replacementHolds, targetNodesHold⟩,
        childrenEquiv.mp targetChildrenHold⟩
  · rintro ⟨sourceNodesHold, sourceChildrenHold⟩
    obtain ⟨removedHolds, targetNodesHold⟩ :=
      nodesEquiv.mp sourceNodesHold
    exact
      ⟨localEquiv.mpr removedHolds, targetNodesHold,
        childrenEquiv.mpr sourceChildrenHold⟩


end SingletonRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
