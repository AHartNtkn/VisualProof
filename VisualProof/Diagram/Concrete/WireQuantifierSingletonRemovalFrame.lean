import VisualProof.Diagram.Concrete.WireQuantifierSingletonRemovalInnerFrame

namespace VisualProof

universe u

namespace ConcreteWireQuantifier

namespace SingletonRemovalSemantics

private abbrev Target
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :=
  ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate source removed

private abbrev targetRegion
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId) :
    (Target source removed).RegionId :=
  ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
    source removed region

@[simp] private theorem targetRegion_eq
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId) :
    targetRegion source removed region = region := by
  apply Fin.ext
  rfl

private theorem targetRegion_injective
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId) :
    Function.Injective (targetRegion source removed) := by
  intro left right same
  apply Fin.ext
  exact congrArg Fin.val same

private theorem target_childrenOf
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (region : source.val.RegionId) :
    (Target source removed).childrenOf (targetRegion source removed region) =
      (source.val.childrenOf region).map
        (targetRegion source removed) := by
  change
    (Target source removed).childrenOf region =
      (source.val.childrenOf region).map (targetRegion source removed)
  have mapped :
      (source.val.childrenOf region).map (targetRegion source removed) =
        source.val.childrenOf region := by
    induction source.val.childrenOf region with
    | nil => rfl
    | cons head tail induction =>
        simp only [List.map_cons, targetRegion_eq, induction]
  rw [mapped]
  unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
  apply List.filter_congr
  intro child _
  generalize dataEquation : source.val.regions child = data
  cases data <;>
    simp [ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate,
      dataEquation]

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

private theorem enclosing_children_unique
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

private theorem removed_not_mem_nodesAt_of_ne
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

private theorem compileNodes_cast_context
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

private theorem denoteItemSeq_cast
    {left right : List Sig}
    (same : left = right)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (items : ItemSeq definitions left)
    (env : Env pre right) :
    denoteItemSeq pre definitionEnv env (same ▸ items) ↔
      denoteItemSeq pre definitionEnv (same.symm ▸ env) items := by
  subst right
  rfl

private theorem denoteRegion_cast
    {left right : List Sig}
    (same : left = right)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (body : Region definitions left)
    (env : Env pre right) :
    denoteRegion pre definitionEnv env (same ▸ body) ↔
      denoteRegion pre definitionEnv (same.symm ▸ env) body := by
  subst right
  rfl

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

private theorem LocalReplacementAt.cast
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

private theorem env_comp_cast_renaming
    {sourceSigs targetCanonical targetActual : List Sig}
    (same : targetCanonical = targetActual)
    (rho : WireRenaming sourceSigs targetCanonical)
    (pre : PreModel)
    (targetEnv : Env pre targetActual) :
    Env.comp targetEnv (same ▸ rho) =
      Env.comp (same.symm ▸ targetEnv) rho := by
  subst targetActual
  rfl

private theorem DiagramContext.liftOuter_bindContextFor
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

private theorem DiagramContext.preservesOuter_bindContextFor
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
  funext sig value
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

private theorem cast_symm_cast
    {α : Sort u} {motive : α → Sort v}
    {left right : α}
    (same : left = right)
    (value : motive left) :
    same.symm ▸ (same ▸ value) = value := by
  subst right
  rfl

private theorem cast_itemSeq_singleton
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

private theorem compiledNodes_outside
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

private theorem compiledNodes_outside_extended
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

private theorem erasedNodes_denotation_extended
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

private theorem compiledChildren_equiv
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
private theorem compileRegion_equiv_outside
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

private theorem compileRegion_equiv_outside_extended
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

private theorem siblingFrame_site_eq
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : ConcreteElaboration.WireContext diagram)
    (target : diagram.RegionId)
    (nested : RegionFrame definitions diagram outer) :
    ∀ (leading : ItemSeq definitions outer.sigs)
      (children : List diagram.RegionId)
      (frame : RegionFrame definitions diagram outer),
      compileSiblingFrame? definitions diagram fuel outer target nested
          leading children =
        some frame →
      ∃ visibleEquality : frame.visible = nested.visible,
        congrArg ConcreteElaboration.WireContext.sigs visibleEquality ▸
            frame.siteBody =
          nested.siteBody := by
  intro leading children
  induction children generalizing leading with
  | nil =>
      intro frame accepted
      simp [compileSiblingFrame?] at accepted
  | cons child tail induction =>
      intro frame accepted
      unfold compileSiblingFrame? at accepted
      split at accepted
      · obtain ⟨suffix, suffixCompiled, frameEquation⟩ :=
          Option.bind_eq_some_iff.mp accepted
        have frameExact :
            ({ visible := nested.visible
               siteBody := nested.siteBody
               context := .surround leading (.cut nested.context) suffix } :
              RegionFrame definitions diagram outer) =
              frame :=
          Option.some.inj frameEquation
        subst frame
        exact ⟨rfl, rfl⟩
      · obtain ⟨body, bodyCompiled, recursive⟩ :=
          Option.bind_eq_some_iff.mp accepted
        exact
          induction
            (leading.append (.cons (.cut body) .nil))
            frame recursive

set_option maxHeartbeats 1200000 in
private theorem compileSiblingFrame_replacement
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed : (Target source removed).WellFormed definitions)
    (fuel : Nat)
    (context : ConcreteElaboration.WireContext source.val)
    (region selected : source.val.RegionId)
    (sourceNested :
      RegionFrame definitions source.val (context.extend region))
    (targetNested :
      RegionFrame definitions (Target source removed)
        ((targetContext source removed context).extend
          (targetRegion source removed region)))
    (replacement : Region definitions targetNested.visible.sigs)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (localLaw : Env pre targetNested.visible.sigs → Prop)
    (nestedEquiv :
      ∀ targetEnv :
          Env pre
            ((targetContext source removed context).extend
              (targetRegion source removed region)).sigs,
        (∀ targetVisibleEnv : Env pre targetNested.visible.sigs,
          DiagramContext.PreservesOuter targetNested.context targetEnv
            targetVisibleEnv →
          localLaw targetVisibleEnv) →
        (denoteRegion pre definitionEnv targetEnv
              (targetNested.context.fill
                (replacement.conjoin targetNested.siteBody)) ↔
            denoteRegion pre definitionEnv
              (Env.comp targetEnv
                (extendedContextRenaming source removed context region))
              (sourceNested.context.fill sourceNested.siteBody)))
    (allAbove :
      ∀ child, child ∈ source.val.childrenOf region →
        ConcreteElaboration.ContextAbove source.val
          (context.extend region) child)
    (outsideOther :
      ∀ child, child ∈ source.val.childrenOf region →
        child ≠ selected →
          ¬source.val.Encloses child (source.val.nodes removed).region) :
    ∀ (sourceLeading :
        ItemSeq definitions (context.extend region).sigs)
      (targetLeading :
        ItemSeq definitions
          ((targetContext source removed context).extend
            (targetRegion source removed region)).sigs)
      (children : List source.val.RegionId)
      (childrenSubset :
        ∀ child, child ∈ children →
          child ∈ source.val.childrenOf region)
      (childrenNodup : children.Nodup)
      (selectedMember : selected ∈ children)
      {sourceFrame :
        RegionFrame definitions source.val (context.extend region)}
      {targetFrame :
        RegionFrame definitions (Target source removed)
          ((targetContext source removed context).extend
            (targetRegion source removed region))},
      compileSiblingFrame? definitions source.val fuel
          (context.extend region) selected sourceNested sourceLeading
          children =
        some sourceFrame →
      compileSiblingFrame? definitions (Target source removed) fuel
          ((targetContext source removed context).extend
            (targetRegion source removed region))
          (targetRegion source removed selected) targetNested targetLeading
          (children.map (targetRegion source removed)) =
        some targetFrame →
      (∀ targetEnv,
        denoteItemSeq pre definitionEnv targetEnv targetLeading ↔
          denoteItemSeq pre definitionEnv
            (Env.comp targetEnv
              (extendedContextRenaming source removed context region))
            sourceLeading) →
      ∃ targetVisible : targetFrame.visible = targetNested.visible,
        ∀ (targetEnv :
            Env pre
              ((targetContext source removed context).extend
                (targetRegion source removed region)).sigs),
          (∀ targetVisibleEnv : Env pre targetFrame.visible.sigs,
            DiagramContext.PreservesOuter targetFrame.context targetEnv
              targetVisibleEnv →
            localLaw
              (congrArg ConcreteElaboration.WireContext.sigs
                targetVisible ▸ targetVisibleEnv)) →
          (denoteRegion pre definitionEnv targetEnv
                (targetFrame.context.fill
                  ((congrArg ConcreteElaboration.WireContext.sigs
                      targetVisible.symm ▸ replacement).conjoin
                    targetFrame.siteBody)) ↔
              denoteRegion pre definitionEnv
                (Env.comp targetEnv
                  (extendedContextRenaming source removed context region))
                (sourceFrame.context.fill sourceFrame.siteBody)) := by
  intro sourceLeading targetLeading children
  induction children generalizing sourceLeading targetLeading with
  | nil =>
      intro childrenSubset childrenNodup selectedMember
      simp at selectedMember
  | cons child tail induction =>
      intro childrenSubset childrenNodup selectedMember sourceFrame
        targetFrame sourceCompiled targetCompiled leadingEquiv
      rw [List.nodup_cons] at childrenNodup
      by_cases same : child = selected
      · subst child
        simp only [compileSiblingFrame?, List.map_cons, targetRegion_eq,
          ↓reduceDIte] at sourceCompiled targetCompiled
        obtain ⟨sourceSuffix, sourceSuffixCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨targetSuffix, targetSuffixCompiled, targetFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp targetCompiled
        have sourceExact :
            ({ visible := sourceNested.visible
               siteBody := sourceNested.siteBody
               context :=
                 .surround sourceLeading (.cut sourceNested.context)
                   sourceSuffix } :
              RegionFrame definitions source.val (context.extend region)) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        have targetExact :
            ({ visible := targetNested.visible
               siteBody := targetNested.siteBody
               context :=
                 .surround targetLeading (.cut targetNested.context)
                   targetSuffix } :
              RegionFrame definitions (Target source removed)
                ((targetContext source removed context).extend
                  (targetRegion source removed region))) =
              targetFrame :=
          Option.some.inj targetFrameEquation
        subst sourceFrame
        subst targetFrame
        refine ⟨rfl, ?_⟩
        intro targetEnv localHyp
        have suffixEquiv :=
          compiledChildren_equiv source.val (Target source removed)
            (ConcreteElaboration.compileRegion? definitions source.val fuel)
            (ConcreteElaboration.compileRegion? definitions
              (Target source removed) fuel)
            (context.extend region)
            ((targetContext source removed context).extend
              (targetRegion source removed region))
            (extendedContextRenaming source removed context region)
            (targetRegion source removed) tail sourceSuffixCompiled
            targetSuffixCompiled pre definitionEnv targetEnv
            (by
              intro candidate member sourceBody targetBody
                sourceBodyCompiled targetBodyCompiled
              have fullMember :=
                childrenSubset candidate
                  (List.mem_cons_of_mem selected member)
              exact
                compileRegion_equiv_outside_extended source removed
                  candidateWellFormed fuel context region candidate
                  (allAbove candidate fullMember)
                  (outsideOther candidate fullMember
                    (by
                      intro candidateSelected
                      subst candidate
                      exact childrenNodup.1 member))
                  sourceBodyCompiled targetBodyCompiled pre definitionEnv
                  targetEnv)
        simp only [DiagramContext.fill]
        rw [Region.denote_surround, Region.denote_surround]
        exact and_congr (leadingEquiv targetEnv)
          (and_congr
            (by
              simpa only [denoteRegion, denoteItemSeq_cons,
                denoteItemSeq, denoteItem, and_true] using
                not_congr
                  (nestedEquiv targetEnv (by
                    intro targetVisibleEnv preserves
                    exact localHyp targetVisibleEnv (by
                      simpa [DiagramContext.PreservesOuter,
                        DiagramContext.liftOuter] using preserves))))
            suffixEquiv)
      · have targetDifferent :
            targetRegion source removed child ≠
              targetRegion source removed selected :=
          fun mapped => same (targetRegion_injective source removed mapped)
        simp only [compileSiblingFrame?, List.map_cons, targetRegion_eq, same,
          ↓reduceDIte] at sourceCompiled targetCompiled
        obtain ⟨sourceBody, sourceBodyCompiled, sourceRecursive⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨targetBody, targetBodyCompiled, targetRecursive⟩ :=
          Option.bind_eq_some_iff.mp targetCompiled
        have childMember := childrenSubset child (by simp)
        have bodyEquiv :=
          compileRegion_equiv_outside_extended source removed
            candidateWellFormed fuel context region child
            (allAbove child childMember)
            (outsideOther child childMember same)
            sourceBodyCompiled targetBodyCompiled pre definitionEnv
        apply
          induction
            (sourceLeading.append (.cons (.cut sourceBody) .nil))
            (targetLeading.append (.cons (.cut targetBody) .nil))
            (by
              intro candidate member
              exact childrenSubset candidate
                (List.mem_cons_of_mem child member))
            childrenNodup.2
            (List.mem_of_ne_of_mem (Ne.symm same) selectedMember)
            sourceRecursive targetRecursive
        intro targetEnv
        simp only [denoteItemSeq_append, denoteItemSeq_cons,
          denoteItemSeq_nil, and_true, cut_denotes_negation]
        exact and_congr (leadingEquiv targetEnv)
          (not_congr (bodyEquiv targetEnv))

private theorem compileScopeBody_replacement
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

set_option maxHeartbeats 1800000 in
private theorem compileRegionFrame_replacement
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (candidateWellFormed : (Target source removed).WellFormed definitions) :
    ∀ (fuel : Nat)
      (sourceOuter : ConcreteElaboration.WireContext source.val)
      (targetOuter :
        ConcreteElaboration.WireContext (Target source removed))
      (outerExact :
        targetOuter = targetContext source removed sourceOuter)
      (region : source.val.RegionId)
      (sourceAbove :
        ConcreteElaboration.ContextAbove source.val sourceOuter region)
      (sourceFrame : RegionFrame definitions source.val sourceOuter)
      (targetFrame :
        RegionFrame definitions (Target source removed)
          targetOuter)
      (sourceCompiled :
        compileRegionFrame? definitions source.val
            (source.val.nodes removed).region fuel region sourceOuter =
          some sourceFrame)
      (targetCompiled :
        compileRegionFrame? definitions (Target source removed)
            (targetRegion source removed (source.val.nodes removed).region)
            fuel (targetRegion source removed region)
            targetOuter =
          some targetFrame)
      (visibleExact :
        targetFrame.visible =
          targetContext source removed sourceFrame.visible)
      (replacement : Region definitions targetFrame.visible.sigs)
      (removedItem : Item definitions sourceFrame.visible.sigs)
      (removedCompiled :
        ConcreteElaboration.compileNodes? definitions source.val
            sourceFrame.visible [removed] =
          some (.cons removedItem .nil))
      (pre : PreModel)
      (definitionEnv : DefinitionEnv pre definitions)
      (targetEnv :
        Env pre targetOuter.sigs)
      (localEquiv :
        ∀ targetVisibleEnv : Env pre targetFrame.visible.sigs,
          DiagramContext.PreservesOuter targetFrame.context targetEnv
              targetVisibleEnv →
            LocalReplacementAt source removed sourceFrame.visible
              targetFrame.visible visibleExact replacement removedItem pre
              definitionEnv targetVisibleEnv),
      denoteRegion pre definitionEnv targetEnv
          (targetFrame.context.fill
            (replacement.conjoin targetFrame.siteBody)) ↔
        denoteRegion pre definitionEnv
          (Env.comp
            (congrArg ConcreteElaboration.WireContext.sigs outerExact ▸
              targetEnv)
            (contextRenaming source removed sourceOuter))
          (sourceFrame.context.fill sourceFrame.siteBody) := by
  intro fuel
  induction fuel with
  | zero =>
      intro sourceOuter targetOuter outerExact region sourceAbove
        sourceFrame targetFrame
        sourceCompiled
      simp [compileRegionFrame?] at sourceCompiled
  | succ childFuel induction =>
      intro sourceOuter targetOuter outerExact region sourceAbove sourceFrame
        targetFrame sourceCompiled targetCompiled visibleExact replacement
        removedItem removedCompiled pre definitionEnv targetEnv localEquiv
      subst targetOuter
      by_cases atSite :
          region = (source.val.nodes removed).region
      · subst region
        simp only [compileRegionFrame?, ↓reduceDIte] at sourceCompiled targetCompiled
        obtain ⟨sourceBody, sourceBodyCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨targetBody, targetBodyCompiled, targetFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp targetCompiled
        have sourceExact :
            ({ visible :=
                 sourceOuter.extend (source.val.nodes removed).region
               siteBody := sourceBody
               context :=
                 bindContextFor source.val sourceOuter.ids
                   (source.val.wiresAt (source.val.nodes removed).region)
                   .hole } :
              RegionFrame definitions source.val sourceOuter) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        have targetExact :
            ({ visible :=
                 (targetContext source removed sourceOuter).extend
                   (targetRegion source removed
                     (source.val.nodes removed).region)
               siteBody := targetBody
               context :=
                 bindContextFor (Target source removed)
                   (targetContext source removed sourceOuter).ids
                   ((Target source removed).wiresAt
                     (targetRegion source removed
                       (source.val.nodes removed).region))
                   .hole } :
              RegionFrame definitions (Target source removed)
                (targetContext source removed sourceOuter)) =
              targetFrame :=
          Option.some.inj targetFrameEquation
        subst sourceFrame
        subst targetFrame
        change
          Item definitions
            (sourceOuter.extend (source.val.nodes removed).region).sigs
          at removedItem
        change
          Region definitions
            ((targetContext source removed sourceOuter).extend
              (targetRegion source removed
                (source.val.nodes removed).region)).sigs
          at replacement
        dsimp only at visibleExact localEquiv removedCompiled ⊢
        have sourceExtendedNodup :
            (sourceOuter.extend
              (source.val.nodes removed).region).ids.Nodup :=
          ConcreteElaboration.extend_nodup definitions source.val
            source.property sourceOuter (source.val.nodes removed).region
            sourceAbove
        have visibleProof :
            visibleExact =
              (targetContext_extend source removed sourceOuter
                (source.val.nodes removed).region).symm :=
          Subsingleton.elim _ _
        rw [visibleProof] at localEquiv
        have replacementEquiv :
            ∀ currentTarget :
                Env pre
                  ((targetContext source removed sourceOuter).extend
                    (targetRegion source removed
                      (source.val.nodes removed).region)).sigs,
              DiagramContext.PreservesOuter
                  (definitions := definitions)
                  (bindContextFor (definitions := definitions)
                    (Target source removed)
                    (targetContext source removed sourceOuter).ids
                    ((Target source removed).wiresAt
                      (targetRegion source removed
                        (source.val.nodes removed).region))
                    .hole)
                  targetEnv currentTarget →
              (denoteRegion pre definitionEnv currentTarget replacement ↔
                denoteItem pre definitionEnv
                  (Env.comp currentTarget
                    (extendedContextRenaming source removed sourceOuter
                      (source.val.nodes removed).region))
                  removedItem) := by
          intro currentTarget preserves
          have equivalent := localEquiv currentTarget preserves
          have environments :=
            env_comp_cast_renaming
              (congrArg ConcreteElaboration.WireContext.sigs
                (targetContext_extend source removed sourceOuter
                  (source.val.nodes removed).region))
              (contextRenaming source removed
                (sourceOuter.extend (source.val.nodes removed).region))
              pre currentTarget
          change
            denoteRegion pre definitionEnv currentTarget replacement ↔
              denoteItem pre definitionEnv
                (Env.comp currentTarget
                  (congrArg ConcreteElaboration.WireContext.sigs
                      (targetContext_extend source removed sourceOuter
                        (source.val.nodes removed).region) ▸
                    contextRenaming source removed
                      (sourceOuter.extend
                        (source.val.nodes removed).region)))
                removedItem
          constructor
          · intro replacementHolds
            exact environments.symm ▸ equivalent.mp replacementHolds
          · intro removedHolds
            apply equivalent.mpr
            exact environments ▸ removedHolds
        have coreEquiv :
            ∀ currentTarget :
                Env pre
                  ((targetContext source removed sourceOuter).extend
                    (targetRegion source removed
                      (source.val.nodes removed).region)).sigs,
              DiagramContext.PreservesOuter
                  (definitions := definitions)
                  (bindContextFor (definitions := definitions)
                    (Target source removed)
                    (targetContext source removed sourceOuter).ids
                    ((Target source removed).wiresAt
                      (targetRegion source removed
                        (source.val.nodes removed).region))
                    .hole)
                  targetEnv currentTarget →
              (denoteRegion pre definitionEnv currentTarget
                  (replacement.conjoin targetBody) ↔
                denoteRegion pre definitionEnv
                  (Env.comp currentTarget
                    (extendedContextRenaming source removed sourceOuter
                      (source.val.nodes removed).region))
                  sourceBody) := by
          intro currentTarget preserves
          exact
            compileScopeBody_replacement source removed candidateWellFormed
              childFuel sourceOuter sourceAbove sourceBody targetBody
              sourceBodyCompiled targetBodyCompiled replacement removedItem
              removedCompiled pre definitionEnv currentTarget
              (replacementEquiv currentTarget preserves)
        change
          denoteRegion pre definitionEnv targetEnv
              ((bindContextFor (Target source removed)
                (targetContext source removed sourceOuter).ids
                ((Target source removed).wiresAt
                  (targetRegion source removed
                    (source.val.nodes removed).region))
                .hole).fill
                (replacement.conjoin targetBody)) ↔
            denoteRegion pre definitionEnv
              (Env.comp targetEnv
                (contextRenaming source removed sourceOuter))
              ((bindContextFor source.val sourceOuter.ids
                (source.val.wiresAt (source.val.nodes removed).region)
                .hole).fill
                sourceBody)
        rw [bindContextFor_fill, bindContextFor_fill,
          finishBodyFor_eq_finishRegion, finishBodyFor_eq_finishRegion,
          ConcreteElaboration.denote_finishRegion,
          ConcreteElaboration.denote_finishRegion]
        constructor
        · rintro ⟨targetValues, targetCore⟩
          obtain ⟨sourceValues, environments⟩ :=
            (extendedEnvironment_correspondence source removed sourceOuter
              (source.val.nodes removed).region sourceExtendedNodup pre
              (Env.comp targetEnv
                (contextRenaming source removed sourceOuter))
              targetEnv rfl).2 targetValues
          refine ⟨sourceValues, ?_⟩
          rw [environments]
          exact
            (coreEquiv _
              (DiagramContext.preservesOuter_bindContextFor
                (Target source removed)
                (targetContext source removed sourceOuter)
                (targetRegion source removed
                  (source.val.nodes removed).region)
                .hole pre targetValues targetEnv _ (by
                  unfold DiagramContext.PreservesOuter
                  rfl))).mp targetCore
        · rintro ⟨sourceValues, sourceCore⟩
          obtain ⟨targetValues, environments⟩ :=
            (extendedEnvironment_correspondence source removed sourceOuter
              (source.val.nodes removed).region sourceExtendedNodup pre
              (Env.comp targetEnv
                (contextRenaming source removed sourceOuter))
              targetEnv rfl).1 sourceValues
          refine ⟨targetValues, ?_⟩
          apply
            (coreEquiv _
              (DiagramContext.preservesOuter_bindContextFor
                (Target source removed)
                (targetContext source removed sourceOuter)
                (targetRegion source removed
                  (source.val.nodes removed).region)
                .hole pre targetValues targetEnv _ (by
                  unfold DiagramContext.PreservesOuter
                  rfl))).mpr
          rw [environments] at sourceCore
          exact sourceCore
      · have targetAtSite :
            targetRegion source removed region ≠
              targetRegion source removed (source.val.nodes removed).region :=
          fun same =>
            atSite (targetRegion_injective source removed same)
        simp only [compileRegionFrame?, atSite, targetAtSite,
          ↓reduceDIte] at sourceCompiled targetCompiled
        obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
          Option.bind_eq_some_iff.mp sourceCompiled
        obtain ⟨selected, selectedFound, sourceAfterSelected⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterNodes
        obtain ⟨sourceNested, sourceNestedCompiled, sourceAfterNested⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterSelected
        obtain
          ⟨sourceAround, sourceAroundCompiled, sourceFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterNested
        obtain ⟨targetNodes, targetNodesCompiled, targetAfterNodes⟩ :=
          Option.bind_eq_some_iff.mp targetCompiled
        obtain
          ⟨targetSelected, targetSelectedFound, targetAfterSelected⟩ :=
          Option.bind_eq_some_iff.mp targetAfterNodes
        have targetSelectedExact :
            targetSelected = targetRegion source removed selected := by
          have mapped :=
            erased_find_enclosing source removed
              (source.val.nodes removed).region
              (source.val.childrenOf region)
          rw [selectedFound] at mapped
          rw [target_childrenOf] at targetSelectedFound
          exact
            Option.some.inj (targetSelectedFound.symm.trans mapped)
        subst targetSelected
        obtain ⟨targetNested, targetNestedCompiled, targetAfterNested⟩ :=
          Option.bind_eq_some_iff.mp targetAfterSelected
        obtain
          ⟨targetAround, targetAroundCompiled, targetFrameEquation⟩ :=
          Option.bind_eq_some_iff.mp targetAfterNested
        have sourceExact :
            ({ visible := sourceAround.visible
               siteBody := sourceAround.siteBody
               context :=
                 bindContextFor source.val sourceOuter.ids
                   (source.val.wiresAt region) sourceAround.context } :
              RegionFrame definitions source.val sourceOuter) =
              sourceFrame :=
          Option.some.inj sourceFrameEquation
        have targetExact :
            ({ visible := targetAround.visible
               siteBody := targetAround.siteBody
               context :=
                 bindContextFor (Target source removed)
                   (targetContext source removed sourceOuter).ids
                   ((Target source removed).wiresAt
                     (targetRegion source removed region))
                   targetAround.context } :
              RegionFrame definitions (Target source removed)
                (targetContext source removed sourceOuter)) =
              targetFrame :=
          Option.some.inj targetFrameEquation
        subst sourceFrame
        subst targetFrame
        change Item definitions sourceAround.visible.sigs at removedItem
        change Region definitions targetAround.visible.sigs at replacement
        dsimp only at visibleExact localEquiv removedCompiled ⊢
        obtain ⟨sourceAroundVisible, sourceAroundBody⟩ :=
          siblingFrame_site_eq definitions source.val childFuel
            (sourceOuter.extend region) selected sourceNested sourceNodes
            (source.val.childrenOf region) sourceAround
            sourceAroundCompiled
        obtain ⟨targetAroundVisible, targetAroundBody⟩ :=
          siblingFrame_site_eq definitions (Target source removed)
            childFuel
            ((targetContext source removed sourceOuter).extend
              (targetRegion source removed region))
            (targetRegion source removed selected) targetNested targetNodes
            ((source.val.childrenOf region).map
              (targetRegion source removed))
            targetAround
            (by
              rw [← target_childrenOf]
              exact targetAroundCompiled)
        have nestedVisibleExact :
            targetNested.visible =
              targetContext source removed sourceNested.visible := by
          calc
            targetNested.visible = targetAround.visible :=
              targetAroundVisible.symm
            _ = targetContext source removed sourceAround.visible :=
              visibleExact
            _ = targetContext source removed sourceNested.visible :=
              congrArg (targetContext source removed) sourceAroundVisible
        let nestedReplacement :
            Region definitions targetNested.visible.sigs :=
          congrArg ConcreteElaboration.WireContext.sigs
            targetAroundVisible ▸ replacement
        let nestedRemovedItem :
            Item definitions sourceNested.visible.sigs :=
          congrArg ConcreteElaboration.WireContext.sigs
            sourceAroundVisible ▸ removedItem
        have nestedRemovedCompiled :
            ConcreteElaboration.compileNodes? definitions source.val
                sourceNested.visible [removed] =
              some (.cons nestedRemovedItem .nil) := by
          simpa only [nestedRemovedItem, cast_itemSeq_singleton] using
            (compileNodes_cast_context source.val sourceAroundVisible
              [removed] removedCompiled)
        have selectedMember :
            selected ∈ source.val.childrenOf region :=
          List.mem_of_find?_eq_some selectedFound
        have selectedData :=
          ConcreteElaboration.mem_childrenOf source.val region selected
            selectedMember
        have selectedAbove :
            ConcreteElaboration.ContextAbove source.val
              (sourceOuter.extend region) selected :=
          ConcreteElaboration.extend_above_child definitions source.val
            source.property sourceOuter region selected sourceAbove
            selectedData
        have selectedEncloses :
            source.val.Encloses selected
              (source.val.nodes removed).region :=
          of_decide_eq_true
            (List.find?_some
              (p := fun candidate =>
                decide
                  (source.val.Encloses candidate
                    (source.val.nodes removed).region))
              selectedFound)
        have targetExtendedExact :
            (targetContext source removed sourceOuter).extend
                (targetRegion source removed region) =
              targetContext source removed (sourceOuter.extend region) :=
          (targetContext_extend source removed sourceOuter region).symm
        have nestedEquiv :
            ∀ currentTarget :
                Env pre
                  ((targetContext source removed sourceOuter).extend
                    (targetRegion source removed region)).sigs,
              (∀ targetVisibleEnv : Env pre targetNested.visible.sigs,
                DiagramContext.PreservesOuter targetNested.context
                    currentTarget targetVisibleEnv →
                  LocalReplacementAt source removed sourceNested.visible
                    targetNested.visible nestedVisibleExact
                    nestedReplacement nestedRemovedItem pre definitionEnv
                    targetVisibleEnv) →
              (denoteRegion pre definitionEnv currentTarget
                  (targetNested.context.fill
                    (nestedReplacement.conjoin targetNested.siteBody)) ↔
                denoteRegion pre definitionEnv
                  (Env.comp currentTarget
                    (extendedContextRenaming source removed sourceOuter
                      region))
                  (sourceNested.context.fill sourceNested.siteBody)) := by
          intro currentTarget nestedLocal
          have recursive :=
            induction (sourceOuter.extend region)
              ((targetContext source removed sourceOuter).extend
                (targetRegion source removed region))
              targetExtendedExact selected selectedAbove sourceNested
              targetNested sourceNestedCompiled targetNestedCompiled
              nestedVisibleExact nestedReplacement nestedRemovedItem
              nestedRemovedCompiled pre definitionEnv currentTarget
              nestedLocal
          have environments :=
            env_comp_cast_renaming
              (congrArg ConcreteElaboration.WireContext.sigs
                (targetContext_extend source removed sourceOuter region))
              (contextRenaming source removed (sourceOuter.extend region))
              pre currentTarget
          constructor
          · intro targetHolds
            exact environments.symm ▸ recursive.mp targetHolds
          · intro sourceHolds
            apply recursive.mpr
            exact environments ▸ sourceHolds
        have sourceExtendedNodup :
            (sourceOuter.extend region).ids.Nodup :=
          ConcreteElaboration.extend_nodup definitions source.val
            source.property sourceOuter region sourceAbove
        have leadingEquiv :
            ∀ currentTarget :
                Env pre
                  ((targetContext source removed sourceOuter).extend
                    (targetRegion source removed region)).sigs,
              denoteItemSeq pre definitionEnv currentTarget targetNodes ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp currentTarget
                    (extendedContextRenaming source removed sourceOuter
                      region))
                  sourceNodes := by
          intro currentTarget
          exact
            compiledNodes_outside_extended source removed
              candidateWellFormed sourceOuter region sourceExtendedNodup
              (removed_not_mem_nodesAt_of_ne source removed region atSite)
              sourceNodesCompiled targetNodesCompiled pre definitionEnv
              currentTarget
        have childrenNodup :
            (source.val.childrenOf region).Nodup := by
          unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
          exact
            (Data.Finite.allFin_nodup source.val.regionCount).filter _
        have allChildrenAbove :
            ∀ child, child ∈ source.val.childrenOf region →
              ConcreteElaboration.ContextAbove source.val
                (sourceOuter.extend region) child := by
          intro child member
          exact
            ConcreteElaboration.extend_above_child definitions source.val
              source.property sourceOuter region child sourceAbove
              (ConcreteElaboration.mem_childrenOf source.val region child
                member)
        have allOtherChildrenOutside :
            ∀ child, child ∈ source.val.childrenOf region →
              child ≠ selected →
                ¬source.val.Encloses child
                  (source.val.nodes removed).region := by
          intro child member different childSite
          exact
            different
              (enclosing_children_unique source region child selected
                (source.val.nodes removed).region member selectedMember
                childSite selectedEncloses)
        obtain ⟨replacementVisible, aroundEquiv⟩ :=
          compileSiblingFrame_replacement source removed
            candidateWellFormed childFuel sourceOuter region selected
            sourceNested targetNested nestedReplacement pre definitionEnv
            (fun targetVisibleEnv =>
              LocalReplacementAt source removed sourceNested.visible
                targetNested.visible nestedVisibleExact nestedReplacement
                nestedRemovedItem pre definitionEnv targetVisibleEnv)
            nestedEquiv
            allChildrenAbove allOtherChildrenOutside sourceNodes
            targetNodes (source.val.childrenOf region) (fun _ member => member)
            childrenNodup selectedMember sourceAroundCompiled
            (by
              rw [← target_childrenOf]
              exact targetAroundCompiled)
            leadingEquiv
        have replacementTransport :
            congrArg ConcreteElaboration.WireContext.sigs
                  replacementVisible.symm ▸
                nestedReplacement =
              replacement := by
          unfold nestedReplacement
          have reverseProof :
              congrArg ConcreteElaboration.WireContext.sigs
                  replacementVisible.symm =
                (congrArg ConcreteElaboration.WireContext.sigs
                  targetAroundVisible).symm :=
            Subsingleton.elim _ _
          rw [reverseProof]
          exact
            cast_symm_cast
              (congrArg ConcreteElaboration.WireContext.sigs
                targetAroundVisible) replacement
        have aroundLocal :
            ∀ (targetValues :
                ConcreteElaboration.WireValues pre
                  (((Target source removed).wiresAt
                    (targetRegion source removed region)).map
                      fun wire => ((Target source removed).wires wire).sig))
              (targetAroundEnv : Env pre targetAround.visible.sigs),
              DiagramContext.PreservesOuter targetAround.context
                  (ConcreteElaboration.extendEnvironment
                    (Target source removed)
                    (targetContext source removed sourceOuter)
                    (targetRegion source removed region) targetValues
                    targetEnv)
                  targetAroundEnv →
                LocalReplacementAt source removed sourceNested.visible
                  targetNested.visible nestedVisibleExact nestedReplacement
                  nestedRemovedItem pre definitionEnv
                  (congrArg ConcreteElaboration.WireContext.sigs
                    replacementVisible ▸ targetAroundEnv) := by
          intro targetValues targetAroundEnv preserves
          have fullPreserves :=
            DiagramContext.preservesOuter_bindContextFor
              (Target source removed)
              (targetContext source removed sourceOuter)
              (targetRegion source removed region)
              targetAround.context pre targetValues targetEnv
              targetAroundEnv preserves
          have aroundLaw := localEquiv targetAroundEnv fullPreserves
          have visibleProof :
              replacementVisible = targetAroundVisible :=
            Subsingleton.elim _ _
          rw [visibleProof]
          have casted :=
            LocalReplacementAt.cast source removed sourceAroundVisible
              targetAroundVisible visibleExact nestedVisibleExact replacement
              removedItem pre definitionEnv
              (congrArg ConcreteElaboration.WireContext.sigs
                targetAroundVisible ▸ targetAroundEnv)
              (by
                have environmentTransport :
                    congrArg ConcreteElaboration.WireContext.sigs
                        targetAroundVisible.symm ▸
                      (congrArg ConcreteElaboration.WireContext.sigs
                          targetAroundVisible ▸
                        targetAroundEnv) =
                      targetAroundEnv :=
                  cast_symm_cast
                    (congrArg ConcreteElaboration.WireContext.sigs
                      targetAroundVisible)
                    targetAroundEnv
                rw [environmentTransport]
                exact aroundLaw)
          simpa [nestedReplacement, nestedRemovedItem] using casted
        change
          denoteRegion pre definitionEnv targetEnv
              ((bindContextFor (Target source removed)
                (targetContext source removed sourceOuter).ids
                ((Target source removed).wiresAt
                  (targetRegion source removed region))
                targetAround.context).fill
                (replacement.conjoin targetAround.siteBody)) ↔
            denoteRegion pre definitionEnv
              (Env.comp targetEnv
                (contextRenaming source removed sourceOuter))
              ((bindContextFor source.val sourceOuter.ids
                (source.val.wiresAt region)
                sourceAround.context).fill sourceAround.siteBody)
        rw [bindContextFor_fill, bindContextFor_fill,
          finishBodyFor_eq_finishRegion, finishBodyFor_eq_finishRegion,
          ConcreteElaboration.denote_finishRegion,
          ConcreteElaboration.denote_finishRegion]
        constructor
        · rintro ⟨targetValues, targetCore⟩
          obtain ⟨sourceValues, environments⟩ :=
            (extendedEnvironment_correspondence source removed sourceOuter
              region sourceExtendedNodup pre
              (Env.comp targetEnv
                (contextRenaming source removed sourceOuter))
              targetEnv rfl).2 targetValues
          refine ⟨sourceValues, ?_⟩
          have targetCore' :
              denoteRegion pre definitionEnv
                (ConcreteElaboration.extendEnvironment
                  (Target source removed)
                  (targetContext source removed sourceOuter)
                  (targetRegion source removed region) targetValues targetEnv)
                (targetAround.context.fill
                  ((congrArg ConcreteElaboration.WireContext.sigs
                    replacementVisible.symm ▸ nestedReplacement).conjoin
                    targetAround.siteBody)) := by
            rw [replacementTransport]
            exact targetCore
          have aroundAt :=
            aroundEquiv
              (ConcreteElaboration.extendEnvironment
                (Target source removed)
                (targetContext source removed sourceOuter)
                (targetRegion source removed region) targetValues targetEnv)
              (by
                intro targetAroundEnv preserves
                exact aroundLocal targetValues targetAroundEnv preserves)
          have sourceResult := aroundAt.mp targetCore'
          exact environments.symm ▸ sourceResult
        · rintro ⟨sourceValues, sourceCore⟩
          obtain ⟨targetValues, environments⟩ :=
            (extendedEnvironment_correspondence source removed sourceOuter
              region sourceExtendedNodup pre
              (Env.comp targetEnv
                (contextRenaming source removed sourceOuter))
              targetEnv rfl).1 sourceValues
          refine ⟨targetValues, ?_⟩
          have aroundAt :=
            aroundEquiv
              (ConcreteElaboration.extendEnvironment
                (Target source removed)
                (targetContext source removed sourceOuter)
                (targetRegion source removed region) targetValues targetEnv)
              (by
                intro targetAroundEnv preserves
                exact aroundLocal targetValues targetAroundEnv preserves)
          have targetResult :=
            aroundAt.mpr (environments ▸ sourceCore)
          rw [replacementTransport] at targetResult
          exact targetResult

/--
Retain the paired contexts immediately inside any enclosing region's binders.
The semantic receipt fixes one target environment for that enclosing extended
context and asks for the local replacement law only in descendants preserving
that fixed environment.
-/
theorem PairedGeneratedFrame.enclosing_replacement_receipt
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (erasure : CheckedErasure source removed)
    (region : source.val.RegionId)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (paired :
      PairedGeneratedFrame source removed
        (source.val.nodes removed).region region fuel sourceOuter sourceFrame)
    (removedItem : Item definitions sourceFrame.visible.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceFrame.visible [removed] =
        some (.cons removedItem .nil))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ targetFrame :
        RegionFrame definitions (Target source removed)
          (targetContext source removed sourceOuter),
      compileRegionFrame? definitions (Target source removed)
          (targetRegion source removed (source.val.nodes removed).region)
          fuel (targetRegion source removed region)
          (targetContext source removed sourceOuter) =
        some targetFrame ∧
      ∃ visibleExact :
          targetFrame.visible =
            targetContext source removed sourceFrame.visible,
        ∀ replacement : Region definitions targetFrame.visible.sigs,
          ∃ inner :
              PairedInnerFrame source removed region sourceOuter sourceFrame
                targetFrame,
            inner.ReplacementDenotation visibleExact replacement removedItem
              pre definitionEnv := by
  cases paired with
  | intro targetFrame sourceAbove _ sourceGenerated targetGenerated
      visibleExact =>
    refine ⟨targetFrame, targetGenerated, visibleExact, ?_⟩
    intro replacement
    cases fuel with
    | zero =>
        simp [compileRegionFrame?] at sourceGenerated
    | succ childFuel =>
      by_cases atSite : region = (source.val.nodes removed).region
      · subst region
        simp only [compileRegionFrame?, ↓reduceDIte] at sourceGenerated targetGenerated
        obtain ⟨sourceBody, sourceBodyCompiled, sourceEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceGenerated
        obtain ⟨targetBody, targetBodyCompiled, targetEquation⟩ :=
          Option.bind_eq_some_iff.mp targetGenerated
        have sourceExact :
            ({ visible :=
                 sourceOuter.extend (source.val.nodes removed).region
               siteBody := sourceBody
               context :=
                 bindContextFor source.val sourceOuter.ids
                   (source.val.wiresAt (source.val.nodes removed).region)
                   .hole } :
              RegionFrame definitions source.val sourceOuter) =
              sourceFrame :=
          Option.some.inj sourceEquation
        have targetExact :
            ({ visible :=
                 (targetContext source removed sourceOuter).extend
                   (targetRegion source removed
                     (source.val.nodes removed).region)
               siteBody := targetBody
               context :=
                 bindContextFor (Target source removed)
                   (targetContext source removed sourceOuter).ids
                   ((Target source removed).wiresAt
                     (targetRegion source removed
                       (source.val.nodes removed).region))
                   .hole } :
              RegionFrame definitions (Target source removed)
                (targetContext source removed sourceOuter)) =
              targetFrame :=
          Option.some.inj targetEquation
        subst sourceFrame
        subst targetFrame
        dsimp only at visibleExact removedCompiled ⊢
        let inner :
            PairedInnerFrame source removed
              (source.val.nodes removed).region sourceOuter
              { visible :=
                  sourceOuter.extend (source.val.nodes removed).region
                siteBody := sourceBody
                context :=
                  bindContextFor source.val sourceOuter.ids
                    (source.val.wiresAt
                      (source.val.nodes removed).region) .hole }
              { visible :=
                  (targetContext source removed sourceOuter).extend
                    (targetRegion source removed
                      (source.val.nodes removed).region)
                siteBody := targetBody
                context :=
                  bindContextFor (Target source removed)
                    (targetContext source removed sourceOuter).ids
                    ((Target source removed).wiresAt
                      (targetRegion source removed
                        (source.val.nodes removed).region)) .hole } :=
          ⟨.hole, .hole, rfl, rfl⟩
        refine ⟨inner, ?_⟩
        intro fixedTargetEnv localLaw
        have visibleProof :
            visibleExact =
              (targetContext_extend source removed sourceOuter
                (source.val.nodes removed).region).symm :=
          Subsingleton.elim _ _
        rw [visibleProof] at localLaw
        have localAt := localLaw fixedTargetEnv (by
          unfold DiagramContext.PreservesOuter
          rfl)
        have environments :=
          env_comp_cast_renaming
            (congrArg ConcreteElaboration.WireContext.sigs
              (targetContext_extend source removed sourceOuter
                (source.val.nodes removed).region))
            (contextRenaming source removed
              (sourceOuter.extend (source.val.nodes removed).region))
            pre fixedTargetEnv
        apply
          compileScopeBody_replacement source removed
            erasure.candidate_wellFormed childFuel sourceOuter sourceAbove
            sourceBody targetBody sourceBodyCompiled targetBodyCompiled
            replacement removedItem removedCompiled pre definitionEnv
            fixedTargetEnv
        unfold LocalReplacementAt at localAt
        constructor
        · intro replacementHolds
          exact environments.symm ▸ localAt.mp replacementHolds
        · intro removedHolds
          apply localAt.mpr
          exact environments ▸ removedHolds
      · have targetAtSite :
            targetRegion source removed region ≠
              targetRegion source removed (source.val.nodes removed).region :=
          fun same => atSite (targetRegion_injective source removed same)
        simp only [compileRegionFrame?, atSite, targetAtSite,
          ↓reduceDIte] at sourceGenerated targetGenerated
        obtain ⟨sourceNodes, sourceNodesCompiled, sourceAfterNodes⟩ :=
          Option.bind_eq_some_iff.mp sourceGenerated
        obtain ⟨selected, selectedFound, sourceAfterSelected⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterNodes
        obtain ⟨sourceNested, sourceNestedCompiled, sourceAfterNested⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterSelected
        obtain ⟨sourceAround, sourceAroundCompiled, sourceEquation⟩ :=
          Option.bind_eq_some_iff.mp sourceAfterNested
        obtain ⟨targetNodes, targetNodesCompiled, targetAfterNodes⟩ :=
          Option.bind_eq_some_iff.mp targetGenerated
        obtain ⟨targetSelected, targetSelectedFound, targetAfterSelected⟩ :=
          Option.bind_eq_some_iff.mp targetAfterNodes
        have targetSelectedExact :
            targetSelected = targetRegion source removed selected := by
          have mapped :=
            erased_find_enclosing source removed
              (source.val.nodes removed).region
              (source.val.childrenOf region)
          rw [selectedFound] at mapped
          rw [target_childrenOf] at targetSelectedFound
          exact Option.some.inj (targetSelectedFound.symm.trans mapped)
        subst targetSelected
        obtain ⟨targetNested, targetNestedCompiled, targetAfterNested⟩ :=
          Option.bind_eq_some_iff.mp targetAfterSelected
        obtain ⟨targetAround, targetAroundCompiled, targetEquation⟩ :=
          Option.bind_eq_some_iff.mp targetAfterNested
        have sourceExact :
            ({ visible := sourceAround.visible
               siteBody := sourceAround.siteBody
               context :=
                 bindContextFor source.val sourceOuter.ids
                   (source.val.wiresAt region) sourceAround.context } :
              RegionFrame definitions source.val sourceOuter) =
              sourceFrame :=
          Option.some.inj sourceEquation
        have targetExact :
            ({ visible := targetAround.visible
               siteBody := targetAround.siteBody
               context :=
                 bindContextFor (Target source removed)
                   (targetContext source removed sourceOuter).ids
                   ((Target source removed).wiresAt
                     (targetRegion source removed region))
                   targetAround.context } :
              RegionFrame definitions (Target source removed)
                (targetContext source removed sourceOuter)) =
              targetFrame :=
          Option.some.inj targetEquation
        subst sourceFrame
        subst targetFrame
        dsimp only at visibleExact removedCompiled ⊢
        obtain ⟨sourceAroundVisible, _⟩ :=
          siblingFrame_site_eq definitions source.val childFuel
            (sourceOuter.extend region) selected sourceNested sourceNodes
            (source.val.childrenOf region) sourceAround
            sourceAroundCompiled
        obtain ⟨targetAroundVisible, _⟩ :=
          siblingFrame_site_eq definitions (Target source removed)
            childFuel
            ((targetContext source removed sourceOuter).extend
              (targetRegion source removed region))
            (targetRegion source removed selected) targetNested targetNodes
            ((source.val.childrenOf region).map (targetRegion source removed))
            targetAround (by
              rw [← target_childrenOf]
              exact targetAroundCompiled)
        have nestedVisibleExact :
            targetNested.visible =
              targetContext source removed sourceNested.visible := by
          calc
            targetNested.visible = targetAround.visible :=
              targetAroundVisible.symm
            _ = targetContext source removed sourceAround.visible :=
              visibleExact
            _ = targetContext source removed sourceNested.visible :=
              congrArg (targetContext source removed) sourceAroundVisible
        let nestedReplacement :
            Region definitions targetNested.visible.sigs :=
          congrArg ConcreteElaboration.WireContext.sigs
            targetAroundVisible ▸ replacement
        let nestedRemovedItem :
            Item definitions sourceNested.visible.sigs :=
          congrArg ConcreteElaboration.WireContext.sigs
            sourceAroundVisible ▸ removedItem
        have nestedRemovedCompiled :
            ConcreteElaboration.compileNodes? definitions source.val
                sourceNested.visible [removed] =
              some (.cons nestedRemovedItem .nil) := by
          simpa only [nestedRemovedItem, cast_itemSeq_singleton] using
            (compileNodes_cast_context source.val sourceAroundVisible
              [removed] removedCompiled)
        have selectedMember :
            selected ∈ source.val.childrenOf region :=
          List.mem_of_find?_eq_some selectedFound
        have selectedAbove :
            ConcreteElaboration.ContextAbove source.val
              (sourceOuter.extend region) selected :=
          ConcreteElaboration.extend_above_child definitions source.val
            source.property sourceOuter region selected sourceAbove
            (ConcreteElaboration.mem_childrenOf source.val region selected
              selectedMember)
        have nestedEquiv :
            ∀ fixedTargetEnv :
                Env pre
                  ((targetContext source removed sourceOuter).extend
                    (targetRegion source removed region)).sigs,
              (∀ descendant : Env pre targetNested.visible.sigs,
                DiagramContext.PreservesOuter targetNested.context
                    fixedTargetEnv descendant →
                  LocalReplacementAt source removed sourceNested.visible
                    targetNested.visible nestedVisibleExact
                    nestedReplacement nestedRemovedItem pre definitionEnv
                    descendant) →
              (denoteRegion pre definitionEnv fixedTargetEnv
                    (targetNested.context.fill
                      (nestedReplacement.conjoin targetNested.siteBody)) ↔
                denoteRegion pre definitionEnv
                  (Env.comp fixedTargetEnv
                    (extendedContextRenaming source removed sourceOuter
                      region))
                  (sourceNested.context.fill sourceNested.siteBody)) := by
          intro fixedTargetEnv localLaw
          have recursive :=
            compileRegionFrame_replacement source removed
              erasure.candidate_wellFormed childFuel
              (sourceOuter.extend region)
              ((targetContext source removed sourceOuter).extend
                (targetRegion source removed region))
              (targetContext_extend source removed sourceOuter region).symm
              selected selectedAbove sourceNested targetNested
              sourceNestedCompiled targetNestedCompiled nestedVisibleExact
              nestedReplacement nestedRemovedItem nestedRemovedCompiled pre
              definitionEnv fixedTargetEnv localLaw
          have environments :=
            env_comp_cast_renaming
              (congrArg ConcreteElaboration.WireContext.sigs
                (targetContext_extend source removed sourceOuter region))
              (contextRenaming source removed (sourceOuter.extend region))
              pre fixedTargetEnv
          constructor
          · intro targetHolds
            exact environments.symm ▸ recursive.mp targetHolds
          · intro sourceHolds
            apply recursive.mpr
            exact environments ▸ sourceHolds
        have sourceExtendedNodup :
            (sourceOuter.extend region).ids.Nodup :=
          ConcreteElaboration.extend_nodup definitions source.val
            source.property sourceOuter region sourceAbove
        have leadingEquiv :
            ∀ fixedTargetEnv,
              denoteItemSeq pre definitionEnv fixedTargetEnv targetNodes ↔
                denoteItemSeq pre definitionEnv
                  (Env.comp fixedTargetEnv
                    (extendedContextRenaming source removed sourceOuter
                      region))
                  sourceNodes := by
          intro fixedTargetEnv
          exact
            compiledNodes_outside_extended source removed
              erasure.candidate_wellFormed sourceOuter region
              sourceExtendedNodup
              (removed_not_mem_nodesAt_of_ne source removed region atSite)
              sourceNodesCompiled targetNodesCompiled pre definitionEnv
              fixedTargetEnv
        have childrenNodup :
            (source.val.childrenOf region).Nodup := by
          unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
          exact (Data.Finite.allFin_nodup source.val.regionCount).filter _
        have allAbove :
            ∀ child, child ∈ source.val.childrenOf region →
              ConcreteElaboration.ContextAbove source.val
                (sourceOuter.extend region) child := by
          intro child member
          exact
            ConcreteElaboration.extend_above_child definitions source.val
              source.property sourceOuter region child sourceAbove
              (ConcreteElaboration.mem_childrenOf source.val region child
                member)
        have selectedEncloses :
            source.val.Encloses selected
              (source.val.nodes removed).region :=
          of_decide_eq_true
            (List.find?_some
              (p := fun candidate =>
                decide
                  (source.val.Encloses candidate
                    (source.val.nodes removed).region))
              selectedFound)
        have outsideOther :
            ∀ child, child ∈ source.val.childrenOf region →
              child ≠ selected →
                ¬source.val.Encloses child
                  (source.val.nodes removed).region := by
          intro child member different childSite
          exact different
            (enclosing_children_unique source region child selected
              (source.val.nodes removed).region member selectedMember
              childSite selectedEncloses)
        obtain ⟨replacementVisible, aroundEquiv⟩ :=
          compileSiblingFrame_replacement source removed
            erasure.candidate_wellFormed childFuel sourceOuter region selected
            sourceNested targetNested nestedReplacement pre definitionEnv
            (fun descendant =>
              LocalReplacementAt source removed sourceNested.visible
                targetNested.visible nestedVisibleExact nestedReplacement
                nestedRemovedItem pre definitionEnv descendant)
            nestedEquiv allAbove outsideOther sourceNodes targetNodes
            (source.val.childrenOf region) (fun _ member => member)
            childrenNodup selectedMember sourceAroundCompiled (by
              rw [← target_childrenOf]
              exact targetAroundCompiled)
            leadingEquiv
        have replacementTransport :
            congrArg ConcreteElaboration.WireContext.sigs
                  replacementVisible.symm ▸
                nestedReplacement =
              replacement := by
          unfold nestedReplacement
          have reverseProof :
              congrArg ConcreteElaboration.WireContext.sigs
                  replacementVisible.symm =
                (congrArg ConcreteElaboration.WireContext.sigs
                  targetAroundVisible).symm :=
            Subsingleton.elim _ _
          rw [reverseProof]
          exact
            cast_symm_cast
              (congrArg ConcreteElaboration.WireContext.sigs
                targetAroundVisible) replacement
        let inner :
            PairedInnerFrame source removed region sourceOuter
              { visible := sourceAround.visible
                siteBody := sourceAround.siteBody
                context :=
                  bindContextFor source.val sourceOuter.ids
                    (source.val.wiresAt region) sourceAround.context }
              { visible := targetAround.visible
                siteBody := targetAround.siteBody
                context :=
                  bindContextFor (Target source removed)
                    (targetContext source removed sourceOuter).ids
                    ((Target source removed).wiresAt
                      (targetRegion source removed region))
                    targetAround.context } :=
          ⟨sourceAround.context, targetAround.context, rfl, rfl⟩
        refine ⟨inner, ?_⟩
        intro fixedTargetEnv localLaw
        change
          denoteRegion pre definitionEnv fixedTargetEnv
              (targetAround.context.fill
                (replacement.conjoin targetAround.siteBody)) ↔
            denoteRegion pre definitionEnv
              (Env.comp fixedTargetEnv
                (extendedContextRenaming source removed sourceOuter region))
              (sourceAround.context.fill sourceAround.siteBody)
        rw [← replacementTransport]
        apply aroundEquiv fixedTargetEnv
        intro targetAroundEnv preserves
        have aroundLaw := localLaw targetAroundEnv preserves
        have visibleProof :
            replacementVisible = targetAroundVisible :=
          Subsingleton.elim _ _
        rw [visibleProof]
        have casted :=
          LocalReplacementAt.cast source removed sourceAroundVisible
            targetAroundVisible visibleExact nestedVisibleExact replacement
            removedItem pre definitionEnv
            (congrArg ConcreteElaboration.WireContext.sigs
              targetAroundVisible ▸ targetAroundEnv)
            (by
              have environmentTransport :
                  congrArg ConcreteElaboration.WireContext.sigs
                      targetAroundVisible.symm ▸
                    (congrArg ConcreteElaboration.WireContext.sigs
                        targetAroundVisible ▸ targetAroundEnv) =
                    targetAroundEnv :=
                cast_symm_cast
                  (congrArg ConcreteElaboration.WireContext.sigs
                    targetAroundVisible)
                  targetAroundEnv
              rw [environmentTransport]
              exact aroundLaw)
        simpa [nestedReplacement, nestedRemovedItem] using casted

/--
Expose the two scope bodies immediately before the removed node's scope
binders.  One canonical paired frame supplies the target compiler equation and
visible-context equality.  For any one fixed visible environment, one local
replacement equivalence at that same environment is enough to relate the
replacement-filled target scope body to the source scope body.

In particular, values already present in `sourceOuter` remain fixed in the
visible environment; this theorem neither rebinds them nor requests another
compiler traversal.
-/
theorem PairedGeneratedFrame.fixedScope_replacement_denotation
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (erasure : CheckedErasure source removed)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (paired :
      PairedGeneratedFrame source removed
        (source.val.nodes removed).region
        (source.val.nodes removed).region fuel sourceOuter sourceFrame)
    (removedItem : Item definitions sourceFrame.visible.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceFrame.visible [removed] =
        some (.cons removedItem .nil))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ targetFrame :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetContext source removed sourceOuter),
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
            source removed (source.val.nodes removed).region)
          fuel
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
            source removed (source.val.nodes removed).region)
          (targetContext source removed sourceOuter) =
        some targetFrame ∧
      ∃ visibleExact :
          targetFrame.visible =
            targetContext source removed sourceFrame.visible,
        ∀ (replacement : Region definitions targetFrame.visible.sigs)
          (targetVisibleEnv : Env pre targetFrame.visible.sigs),
          (denoteRegion pre definitionEnv targetVisibleEnv replacement ↔
            denoteItem pre definitionEnv
              (Env.comp
                (congrArg ConcreteElaboration.WireContext.sigs
                    visibleExact ▸
                  targetVisibleEnv)
                (contextRenaming source removed sourceFrame.visible))
              removedItem) →
          (denoteRegion pre definitionEnv targetVisibleEnv
                (replacement.conjoin targetFrame.siteBody) ↔
              denoteRegion pre definitionEnv
                (Env.comp
                  (congrArg ConcreteElaboration.WireContext.sigs
                      visibleExact ▸
                    targetVisibleEnv)
                  (contextRenaming source removed sourceFrame.visible))
                sourceFrame.siteBody) := by
  cases paired with
  | intro targetFrame sourceAbove _ sourceGenerated targetGenerated
      visibleExact =>
      refine ⟨targetFrame, targetGenerated, visibleExact, ?_⟩
      intro replacement targetVisibleEnv localEquiv
      cases fuel with
      | zero =>
          simp [compileRegionFrame?] at sourceGenerated
      | succ childFuel =>
          simp only [compileRegionFrame?, ↓reduceDIte]
            at sourceGenerated targetGenerated
          obtain ⟨sourceBody, sourceBodyCompiled, sourceFrameEquation⟩ :=
            Option.bind_eq_some_iff.mp sourceGenerated
          obtain ⟨targetBody, targetBodyCompiled, targetFrameEquation⟩ :=
            Option.bind_eq_some_iff.mp targetGenerated
          have sourceExact :
              ({ visible :=
                   sourceOuter.extend (source.val.nodes removed).region
                 siteBody := sourceBody
                 context :=
                   bindContextFor source.val sourceOuter.ids
                     (source.val.wiresAt
                       (source.val.nodes removed).region)
                     .hole } :
                RegionFrame definitions source.val sourceOuter) =
                sourceFrame :=
            Option.some.inj sourceFrameEquation
          have targetExact :
              ({ visible :=
                   (targetContext source removed sourceOuter).extend
                     (targetRegion source removed
                       (source.val.nodes removed).region)
                 siteBody := targetBody
                 context :=
                   bindContextFor (Target source removed)
                     (targetContext source removed sourceOuter).ids
                     ((Target source removed).wiresAt
                       (targetRegion source removed
                         (source.val.nodes removed).region))
                     .hole } :
                RegionFrame definitions (Target source removed)
                  (targetContext source removed sourceOuter)) =
                targetFrame :=
            Option.some.inj targetFrameEquation
          subst sourceFrame
          subst targetFrame
          change
            Item definitions
              (sourceOuter.extend (source.val.nodes removed).region).sigs
            at removedItem
          change
            Region definitions
              ((targetContext source removed sourceOuter).extend
                (targetRegion source removed
                  (source.val.nodes removed).region)).sigs
            at replacement
          dsimp only at visibleExact localEquiv removedCompiled ⊢
          have visibleProof :
              visibleExact =
                (targetContext_extend source removed sourceOuter
                  (source.val.nodes removed).region).symm :=
            Subsingleton.elim _ _
          rw [visibleProof] at localEquiv ⊢
          have environments :=
            env_comp_cast_renaming
              (congrArg ConcreteElaboration.WireContext.sigs
                (targetContext_extend source removed sourceOuter
                  (source.val.nodes removed).region))
              (contextRenaming source removed
                (sourceOuter.extend (source.val.nodes removed).region))
              pre targetVisibleEnv
          have replacementEquiv :
              denoteRegion pre definitionEnv targetVisibleEnv replacement ↔
                denoteItem pre definitionEnv
                  (Env.comp targetVisibleEnv
                    (extendedContextRenaming source removed sourceOuter
                      (source.val.nodes removed).region))
                  removedItem := by
            change
              denoteRegion pre definitionEnv targetVisibleEnv replacement ↔
                denoteItem pre definitionEnv
                  (Env.comp targetVisibleEnv
                    (congrArg ConcreteElaboration.WireContext.sigs
                        (targetContext_extend source removed sourceOuter
                          (source.val.nodes removed).region) ▸
                      contextRenaming source removed
                        (sourceOuter.extend
                          (source.val.nodes removed).region)))
                  removedItem
            constructor
            · intro replacementHolds
              exact environments.symm ▸ localEquiv.mp replacementHolds
            · intro removedHolds
              apply localEquiv.mpr
              exact environments ▸ removedHolds
          have bodyEquiv :=
            compileScopeBody_replacement source removed
              erasure.candidate_wellFormed childFuel sourceOuter sourceAbove
              sourceBody targetBody sourceBodyCompiled targetBodyCompiled
              replacement removedItem removedCompiled pre definitionEnv
              targetVisibleEnv replacementEquiv
          constructor
          · intro targetHolds
            exact environments ▸ bodyEquiv.mp targetHolds
          · intro sourceHolds
            exact bodyEquiv.mpr (environments.symm ▸ sourceHolds)

/--
Expose the target half of one canonical paired singleton-erasure frame together
with fixed-environment replacement semantics.  The sole semantic premise is
the local equivalence between the arbitrary replacement and the compiled
removed singleton under the canonical visible-environment pullback.
-/
theorem PairedGeneratedFrame.replacement_denotation
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (erasure : CheckedErasure source removed)
    (region : source.val.RegionId)
    (fuel : Nat)
    (sourceOuter : ConcreteElaboration.WireContext source.val)
    (sourceFrame : RegionFrame definitions source.val sourceOuter)
    (paired :
      PairedGeneratedFrame source removed
        (source.val.nodes removed).region region fuel sourceOuter sourceFrame)
    (removedItem : Item definitions sourceFrame.visible.sigs)
    (removedCompiled :
      ConcreteElaboration.compileNodes? definitions source.val
          sourceFrame.visible [removed] =
        some (.cons removedItem .nil))
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions) :
    ∃ targetFrame :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (targetContext source removed sourceOuter),
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            source removed)
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
            source removed (source.val.nodes removed).region)
          fuel
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
            source removed region)
          (targetContext source removed sourceOuter) =
        some targetFrame ∧
      ∃ visibleExact :
          targetFrame.visible =
            targetContext source removed sourceFrame.visible,
        ∀ (replacement : Region definitions targetFrame.visible.sigs),
          (∀ targetVisibleEnv : Env pre targetFrame.visible.sigs,
            denoteRegion pre definitionEnv targetVisibleEnv replacement ↔
              denoteItem pre definitionEnv
                (Env.comp
                  (congrArg ConcreteElaboration.WireContext.sigs
                      visibleExact ▸
                    targetVisibleEnv)
                  (contextRenaming source removed sourceFrame.visible))
                removedItem) →
          ∀ targetOuterEnv :
              Env pre (targetContext source removed sourceOuter).sigs,
            denoteRegion pre definitionEnv targetOuterEnv
                (targetFrame.context.fill
                  (replacement.conjoin targetFrame.siteBody)) ↔
              denoteRegion pre definitionEnv
                (Env.comp targetOuterEnv
                  (contextRenaming source removed sourceOuter))
                (sourceFrame.context.fill sourceFrame.siteBody) := by
  cases paired with
  | intro targetFrame sourceAbove targetAbove sourceGenerated targetGenerated
      visibleExact =>
      refine ⟨targetFrame, targetGenerated, visibleExact, ?_⟩
      intro replacement localEquiv targetOuterEnv
      exact
        compileRegionFrame_replacement source removed
          erasure.candidate_wellFormed fuel sourceOuter
          (targetContext source removed sourceOuter) rfl region sourceAbove
          sourceFrame targetFrame sourceGenerated targetGenerated visibleExact
          replacement removedItem removedCompiled pre definitionEnv
          targetOuterEnv (fun targetVisibleEnv _ =>
            localEquiv targetVisibleEnv)

end SingletonRemovalSemantics

end ConcreteWireQuantifier

end VisualProof
