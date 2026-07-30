import VisualProof.Diagram.Concrete.Elaborate

namespace VisualProof

universe u

namespace ConcreteElaboration

private theorem compileNodes?_item_for_node
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : WireContext diagram) :
    ∀ {nodes : List diagram.NodeId}
      {items : ItemSeq definitions context.sigs},
      compileNodes? definitions diagram context nodes = some items →
      ∀ node, node ∈ nodes →
        ∃ item,
          item ∈ items.toList ∧
          compileNodes? definitions diagram context [node] =
            some (.cons item .nil)
  | [], _, _, _, member => by simp at member
  | head :: tail, items, compiled, node, member => by
      obtain ⟨headItem, tailItems, headCompiled, tailCompiled, itemsExact⟩ :=
        compileNodes?_cons_components definitions diagram context head tail
          items compiled
      subst items
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨headItem, by simp [ItemSeq.toList], headCompiled⟩
      · obtain ⟨item, itemMember, itemCompiled⟩ :=
          compileNodes?_item_for_node definitions diagram context tailCompiled
            node tailMember
        exact ⟨item, by simp [ItemSeq.toList, itemMember], itemCompiled⟩

private theorem compileNodes?_node_for_item
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : WireContext diagram) :
    ∀ {nodes : List diagram.NodeId}
      {items : ItemSeq definitions context.sigs},
      compileNodes? definitions diagram context nodes = some items →
      ∀ item, item ∈ items.toList →
        ∃ node,
          node ∈ nodes ∧
          compileNodes? definitions diagram context [node] =
            some (.cons item .nil)
  | [], items, compiled, item, member => by
      have itemsExact : (.nil : ItemSeq definitions context.sigs) = items :=
        Option.some.inj (by simpa [compileNodes?] using compiled)
      subst items
      simp [ItemSeq.toList] at member
  | head :: tail, items, compiled, item, member => by
      obtain ⟨headItem, tailItems, headCompiled, tailCompiled, itemsExact⟩ :=
        compileNodes?_cons_components definitions diagram context head tail
          items compiled
      subst items
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨head, by simp, headCompiled⟩
      · obtain ⟨node, nodeMember, itemCompiled⟩ :=
          compileNodes?_node_for_item definitions diagram context tailCompiled
            item tailMember
        exact ⟨node, by simp [nodeMember], itemCompiled⟩

theorem compileNodes?_iso_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    (contexts : WireContextsCorrespond iso leftContext rightContext)
    {pre : PreModel}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (envs : EnvironmentsCorrespond iso leftContext rightContext
      leftEnv rightEnv)
    {leftNodes : List left.NodeId} {rightNodes : List right.NodeId}
    (forwardNodes :
      ∀ node, node ∈ leftNodes → iso.nodes node ∈ rightNodes)
    (backwardNodes :
      ∀ node, node ∈ rightNodes → iso.nodes.symm node ∈ leftNodes)
    {leftItems : ItemSeq definitions leftContext.sigs}
    {rightItems : ItemSeq definitions rightContext.sigs}
    (leftCompiled :
      compileNodes? definitions left leftContext leftNodes = some leftItems)
    (rightCompiled :
      compileNodes? definitions right rightContext rightNodes =
        some rightItems) :
    denoteItemSeq pre definitionEnv leftEnv leftItems ↔
      denoteItemSeq pre definitionEnv rightEnv rightItems := by
  rw [ItemSeq.denote_iff_mem, ItemSeq.denote_iff_mem]
  constructor
  · intro leftDenotes rightItem rightMember
    obtain ⟨rightNode, rightNodeMember, rightItemCompiled⟩ :=
      compileNodes?_node_for_item definitions right rightContext
        rightCompiled rightItem rightMember
    let leftNode := iso.nodes.symm rightNode
    have leftNodeMember : leftNode ∈ leftNodes :=
      backwardNodes rightNode rightNodeMember
    obtain ⟨leftItem, leftItemMember, leftItemCompiled⟩ :=
      compileNodes?_item_for_node definitions left leftContext leftCompiled
        leftNode leftNodeMember
    obtain ⟨mappedItem, mappedCompiled, itemDenotation⟩ :=
      compileNodes?_singleton_forward_denotation iso leftWellFormed rightWellFormed
        contexts definitionEnv envs leftNode leftItem leftItemCompiled
    have mappedNode : iso.nodes leftNode = rightNode :=
      iso.nodes.right_inv rightNode
    have mappedItemEquality : mappedItem = rightItem := by
      rw [mappedNode] at mappedCompiled
      exact
        (ItemSeq.cons.inj
          (Option.some.inj
            (mappedCompiled.symm.trans rightItemCompiled))).1
    subst mappedItem
    exact itemDenotation.mp (leftDenotes leftItem leftItemMember)
  · intro rightDenotes leftItem leftMember
    obtain ⟨leftNode, leftNodeMember, leftItemCompiled⟩ :=
      compileNodes?_node_for_item definitions left leftContext leftCompiled
        leftItem leftMember
    obtain ⟨rightItem, rightItemCompiled, itemDenotation⟩ :=
      compileNodes?_singleton_forward_denotation iso leftWellFormed rightWellFormed
        contexts definitionEnv envs leftNode leftItem leftItemCompiled
    have rightNodeMember : iso.nodes leftNode ∈ rightNodes :=
      forwardNodes leftNode leftNodeMember
    obtain ⟨storedItem, storedMember, storedCompiled⟩ :=
      compileNodes?_item_for_node definitions right rightContext rightCompiled
        (iso.nodes leftNode) rightNodeMember
    have storedEquality : storedItem = rightItem := by
      exact
        (ItemSeq.cons.inj
          (Option.some.inj
            (storedCompiled.symm.trans rightItemCompiled))).1
    subst storedItem
    exact itemDenotation.mpr (rightDenotes rightItem storedMember)

private theorem compileRegion?_forward_denotation
    {definitions : List (List Sig)}
    {pre : PreModel.{u}}
    (definitionEnv : DefinitionEnv pre definitions) :
    ∀ fuel {left right : ConcreteDiagram definitions.length}
      (iso : ConcreteIso left right)
      (_leftWellFormed : left.WellFormed definitions)
      (_rightWellFormed : right.WellFormed definitions)
      {leftContext : WireContext left}
      {rightContext : WireContext right}
      (contexts : WireContextsCorrespond iso leftContext rightContext)
      {region : left.RegionId}
      (_leftAbove : ContextAbove left leftContext region)
      (_rightAbove :
        ContextAbove right rightContext (iso.regions region))
      (leftEnv : Env pre leftContext.sigs)
      {leftBody rightBody},
      compileRegion? definitions left fuel region leftContext =
        some leftBody →
      compileRegion? definitions right fuel (iso.regions region)
          rightContext = some rightBody →
      denoteRegion pre definitionEnv leftEnv leftBody →
        denoteRegion pre definitionEnv
          (pullEnvironment iso contexts leftEnv) rightBody := by
  intro fuel
  induction fuel with
  | zero =>
      intro left right iso leftWellFormed rightWellFormed leftContext
        rightContext contexts region leftAbove rightAbove leftEnv
        leftBody rightBody leftCompiled
      simp [compileRegion?] at leftCompiled
  | succ fuel induction =>
      intro left right iso leftWellFormed rightWellFormed leftContext
        rightContext contexts region leftAbove rightAbove leftEnv
        leftBody rightBody leftCompiled rightCompiled leftDenotes
      simp only [compileRegion?] at leftCompiled rightCompiled
      cases leftNodesEquation :
          compileNodes? definitions left (leftContext.extend region)
            (left.nodesAt region) with
      | none =>
          rw [leftNodesEquation] at leftCompiled
          simp at leftCompiled
      | some leftNodes =>
          rw [leftNodesEquation] at leftCompiled
          cases leftChildrenEquation :
              compileChildrenWith? definitions left
                (compileRegion? definitions left fuel)
                (leftContext.extend region) (left.childrenOf region) with
          | none =>
              rw [leftChildrenEquation] at leftCompiled
              simp at leftCompiled
          | some leftChildren =>
              rw [leftChildrenEquation] at leftCompiled
              cases rightNodesEquation :
                  compileNodes? definitions right
                    (rightContext.extend (iso.regions region))
                    (right.nodesAt (iso.regions region)) with
              | none =>
                  rw [rightNodesEquation] at rightCompiled
                  simp at rightCompiled
              | some rightNodes =>
                  rw [rightNodesEquation] at rightCompiled
                  cases rightChildrenEquation :
                      compileChildrenWith? definitions right
                        (compileRegion? definitions right fuel)
                        (rightContext.extend (iso.regions region))
                        (right.childrenOf (iso.regions region)) with
                  | none =>
                      rw [rightChildrenEquation] at rightCompiled
                      simp at rightCompiled
                  | some rightChildren =>
                      rw [rightChildrenEquation] at rightCompiled
                      have leftBodyEquality :
                          finishRegion left leftContext region
                              (.mk (leftNodes.append leftChildren)) =
                            leftBody :=
                        Option.some.inj leftCompiled
                      have rightBodyEquality :
                          finishRegion right rightContext (iso.regions region)
                              (.mk (rightNodes.append rightChildren)) =
                            rightBody :=
                        Option.some.inj rightCompiled
                      subst leftBody
                      subst rightBody
                      rw [denote_finishRegion] at leftDenotes
                      rw [denote_finishRegion]
                      obtain ⟨leftValues, leftCoreDenotes⟩ := leftDenotes
                      let extendedContexts :=
                        extend_contexts_correspond iso contexts region
                      let leftExtendedEnv :=
                        extendEnvironment left leftContext region leftValues
                          leftEnv
                      let rightExtendedEnv :=
                        pullEnvironment iso extendedContexts leftExtendedEnv
                      let rightValues :=
                        valuesFromEnvironmentFor right rightContext.ids
                          (right.wiresAt (iso.regions region))
                          rightExtendedEnv
                      refine ⟨rightValues, ?_⟩
                      have extendedNodup :=
                        extend_nodup definitions left leftWellFormed
                          leftContext region leftAbove
                      have rightEnvironmentEquality :
                          extendEnvironment right rightContext
                              (iso.regions region) rightValues
                              (pullEnvironment iso contexts leftEnv) =
                            rightExtendedEnv :=
                        extendEnvironmentFor_from right rightContext.ids
                          (right.wiresAt (iso.regions region))
                          rightExtendedEnv
                          (pullEnvironment iso contexts leftEnv)
                          (fun _ rightVar =>
                            pullEnvironment_extend_agrees iso contexts region
                              extendedNodup leftEnv leftValues rightVar)
                      rw [rightEnvironmentEquality]
                      change denoteItemSeq pre definitionEnv leftExtendedEnv
                        (leftNodes.append leftChildren) at leftCoreDenotes
                      change denoteItemSeq pre definitionEnv rightExtendedEnv
                        (rightNodes.append rightChildren)
                      rw [denoteItemSeq_append] at leftCoreDenotes ⊢
                      constructor
                      · exact (compileNodes?_iso_denotation iso leftWellFormed
                          rightWellFormed extendedContexts definitionEnv
                          (pull_environments_correspond iso extendedContexts
                            leftExtendedEnv)
                          (fun _ member => iso.nodesAt_forward member)
                          (fun node
                            (member : node ∈
                              right.nodesAt (iso.regions region)) => by
                            have pulled := iso.nodesAt_backward member
                            have regionEquality :
                                iso.regions.symm (iso.regions region) = region :=
                              iso.regions.left_inv region
                            rw [regionEquality] at pulled
                            exact pulled)
                          leftNodesEquation rightNodesEquation).mp
                            leftCoreDenotes.1
                      · apply (compileChildrenWith?_iso_denotation iso
                          definitionEnv
                          (compileRegion? definitions left fuel)
                          (compileRegion? definitions right fuel)
                          (fun _ member => iso.childrenOf_forward member)
                          (fun child
                            (member : child ∈
                              right.childrenOf (iso.regions region)) => by
                            have pulled := iso.childrenOf_backward member
                            have regionEquality :
                                iso.regions.symm (iso.regions region) = region :=
                              iso.regions.left_inv region
                            rw [regionEquality] at pulled
                            exact pulled)
                          ?_ leftChildrenEquation rightChildrenEquation).mp
                            leftCoreDenotes.2
                        intro child childMember childBody childCompiled
                        have targetMember :=
                          iso.childrenOf_forward childMember
                        obtain ⟨targetBody, _, targetCompiled⟩ :=
                          compileChildrenWith?_item_for_child definitions right
                            (compileRegion? definitions right fuel)
                            (rightContext.extend (iso.regions region))
                            rightChildrenEquation (iso.regions child)
                            targetMember
                        have childData :=
                          mem_childrenOf left region child childMember
                        have childAbove := extend_above_child definitions left
                          leftWellFormed leftContext region child leftAbove
                          childData
                        have targetChildData := mem_childrenOf right
                          (iso.regions region) (iso.regions child) targetMember
                        have targetChildAbove := extend_above_child definitions
                          right rightWellFormed rightContext
                          (iso.regions region) (iso.regions child) rightAbove
                          targetChildData
                        refine ⟨targetBody, targetCompiled, ?_⟩
                        constructor
                        · exact induction iso leftWellFormed rightWellFormed
                            extendedContexts childAbove targetChildAbove
                            leftExtendedEnv childCompiled targetCompiled
                        · intro targetDenotes
                          have childRoundtrip :
                              iso.regions.symm (iso.regions child) = child :=
                            iso.regions.left_inv child
                          have childAbove' :
                              ContextAbove left (leftContext.extend region)
                                (iso.symm.regions (iso.regions child)) := by
                            simpa [ConcreteIso.symm, childRoundtrip] using
                              childAbove
                          have childCompiled' :
                              compileRegion? definitions left fuel
                                  (iso.symm.regions (iso.regions child))
                                  (leftContext.extend region) =
                                some childBody := by
                            simpa [ConcreteIso.symm, childRoundtrip] using
                              childCompiled
                          have reversed := induction iso.symm rightWellFormed
                            leftWellFormed extendedContexts.symm
                            targetChildAbove childAbove' rightExtendedEnv
                            targetCompiled childCompiled' targetDenotes
                          have roundtrip := pullEnvironment_roundtrip iso
                            extendedContexts extendedNodup leftExtendedEnv
                          rw [roundtrip] at reversed
                          exact reversed

private theorem compileRoot?_forward_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    (leftWellFormed : left.WellFormed definitions)
    (rightWellFormed : right.WellFormed definitions)
    {pre : PreModel.{u}}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftBody rightBody : Region definitions []}
    (leftCompiled : compileRoot? definitions left = some leftBody)
    (rightCompiled : compileRoot? definitions right = some rightBody)
    (leftDenotes : denoteRegion pre definitionEnv Env.empty leftBody) :
    denoteRegion pre definitionEnv Env.empty rightBody := by
  unfold compileRoot? at leftCompiled rightCompiled
  rw [← iso.regionCount_eq, ← iso.root] at rightCompiled
  have emptyAbove : ContextAbove left (WireContext.empty left) left.root :=
    ⟨by simp [WireContext.empty], by
      intro wire member
      simp [WireContext.empty] at member⟩
  have targetEmptyAbove :
      ContextAbove right (WireContext.empty right) (iso.regions left.root) :=
    ⟨by simp [WireContext.empty], by
      intro wire member
      simp [WireContext.empty] at member⟩
  have forwarded := compileRegion?_forward_denotation definitionEnv
    (left.regionCount + 1) iso leftWellFormed rightWellFormed
    (empty_contexts_correspond iso)
    (region := left.root) emptyAbove targetEmptyAbove Env.empty
    leftCompiled rightCompiled leftDenotes
  have pulledEmpty :
      pullEnvironment iso (empty_contexts_correspond iso)
          (Env.empty : Env pre []) = Env.empty := by
    funext sig value
    nomatch value
  rw [pulledEmpty] at forwarded
  exact forwarded

end ConcreteElaboration

theorem iso_denotation
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (iso : ConcreteIso left.val right.val)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv left ↔
      denoteChecked pre definitionEnv right := by
  rw [elaborate_denotes_checked, elaborate_denotes_checked]
  have leftCompiled := elaborateWith_compiles definitions left.val left.property
  have rightCompiled :=
    elaborateWith_compiles definitions right.val right.property
  constructor
  · exact ConcreteElaboration.compileRoot?_forward_denotation iso
      left.property right.property definitionEnv leftCompiled rightCompiled
  · exact ConcreteElaboration.compileRoot?_forward_denotation iso.symm
      right.property left.property definitionEnv rightCompiled leftCompiled

end VisualProof
