import VisualProof.Diagram.Concrete.ElaborationNodeCompletion

namespace VisualProof

namespace ConcreteElaboration

private theorem mem_nodesAt
    (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) (node : diagram.NodeId)
    (member : node ∈ diagram.nodesAt region) :
    (diagram.nodes node).region = region := by
  unfold ConcreteDiagram.nodesAt at member
  simp only [List.mem_filter] at member
  exact eq_of_beq member.2

theorem mem_childrenOf
    (diagram : ConcreteDiagram definitionCount)
    (region child : diagram.RegionId)
    (member : child ∈ diagram.childrenOf region) :
    diagram.regions child = .cut region := by
  unfold ConcreteDiagram.childrenOf at member
  simp only [List.mem_filter] at member
  rcases member with ⟨_, checked⟩
  cases childData : diagram.regions child with
  | sheet => simp [childData] at checked
  | cut parent =>
      rw [childData] at checked
      have equality : parent = region := by
        exact eq_of_beq checked
      subst parent
      rfl

private theorem compileChildrenWith?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : WireContext diagram) →
      Option (Region definitions context.sigs))
    (context : WireContext diagram) :
    (children : List diagram.RegionId) →
    (∀ child, child ∈ children →
      ∃ body, recurse child context = some body) →
    ∃ items,
      compileChildrenWith? definitions diagram recurse context children =
        some items
  | [], _ => ⟨.nil, rfl⟩
  | child :: tail, complete => by
      obtain ⟨body, bodyCompiled⟩ := complete child (by simp)
      obtain ⟨rest, restCompiled⟩ :=
        compileChildrenWith?_complete definitions diagram recurse context tail
          (by
            intro candidate member
            exact complete candidate (by simp [member]))
      exact ⟨.cons (.cut body) rest, by
        simp [compileChildrenWith?, bodyCompiled, restCompiled]⟩

theorem compileChildrenWith?_item_for_child
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : WireContext diagram) →
      Option (Region definitions context.sigs))
    (context : WireContext diagram) :
    ∀ {children : List diagram.RegionId}
      {items : ItemSeq definitions context.sigs},
      compileChildrenWith? definitions diagram recurse context children =
        some items →
      ∀ child, child ∈ children →
        ∃ body,
          (.cut body : Item definitions context.sigs) ∈ items.toList ∧
          recurse child context = some body
  | [], _, compiled, child, member => by simp at member
  | head :: tail, items, compiled, child, member => by
      cases headEquation : recurse head context with
      | none => simp [compileChildrenWith?, headEquation] at compiled
      | some headBody =>
          cases tailEquation :
              compileChildrenWith? definitions diagram recurse context tail with
          | none =>
              simp [compileChildrenWith?, headEquation, tailEquation] at compiled
          | some tailItems =>
              have itemsEquality :
                  (ItemSeq.cons (.cut headBody) tailItems :
                    ItemSeq definitions context.sigs) = items := by
                exact Option.some.inj (by
                  simpa [compileChildrenWith?, headEquation, tailEquation]
                    using compiled)
              subst items
              simp only [List.mem_cons] at member
              rcases member with rfl | tailMember
              · exact ⟨headBody, by simp [ItemSeq.toList], headEquation⟩
              · obtain ⟨body, itemMember, bodyCompiled⟩ :=
                  compileChildrenWith?_item_for_child definitions diagram
                    recurse context tailEquation child tailMember
                exact ⟨body, by
                  simp [ItemSeq.toList, itemMember], bodyCompiled⟩

private theorem compileChildrenWith?_child_for_item
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (recurse : (region : diagram.RegionId) →
      (context : WireContext diagram) →
      Option (Region definitions context.sigs))
    (context : WireContext diagram) :
    ∀ {children : List diagram.RegionId}
      {items : ItemSeq definitions context.sigs},
      compileChildrenWith? definitions diagram recurse context children =
        some items →
      ∀ item, item ∈ items.toList →
        ∃ child body,
          child ∈ children ∧
          recurse child context = some body ∧
          item = .cut body
  | [], items, compiled, item, member => by
      have itemsEquality : (.nil : ItemSeq definitions context.sigs) = items :=
        Option.some.inj (by
          simpa [compileChildrenWith?] using compiled)
      subst items
      simp [ItemSeq.toList] at member
  | head :: tail, items, compiled, item, member => by
      cases headEquation : recurse head context with
      | none => simp [compileChildrenWith?, headEquation] at compiled
      | some headBody =>
          cases tailEquation :
              compileChildrenWith? definitions diagram recurse context tail with
          | none =>
              simp [compileChildrenWith?, headEquation, tailEquation] at compiled
          | some tailItems =>
              have itemsEquality :
                  (ItemSeq.cons (.cut headBody) tailItems :
                    ItemSeq definitions context.sigs) = items := by
                exact Option.some.inj (by
                  simpa [compileChildrenWith?, headEquation, tailEquation]
                    using compiled)
              subst items
              simp only [ItemSeq.toList, List.mem_cons] at member
              rcases member with rfl | tailMember
              · exact ⟨head, headBody, by simp, headEquation, rfl⟩
              · obtain ⟨child, body, childMember, bodyCompiled, itemEquality⟩ :=
                  compileChildrenWith?_child_for_item definitions diagram
                    recurse context tailEquation item tailMember
                exact ⟨child, body, by simp [childMember],
                  bodyCompiled, itemEquality⟩

theorem compileChildrenWith?_iso_denotation
    {definitions : List (List Sig)}
    {left right : ConcreteDiagram definitions.length}
    (iso : ConcreteIso left right)
    {leftContext : WireContext left}
    {rightContext : WireContext right}
    {pre : PreModel}
    (definitionEnv : DefinitionEnv pre definitions)
    {leftEnv : Env pre leftContext.sigs}
    {rightEnv : Env pre rightContext.sigs}
    (leftRecurse : (region : left.RegionId) →
      (context : WireContext left) →
      Option (Region definitions context.sigs))
    (rightRecurse : (region : right.RegionId) →
      (context : WireContext right) →
      Option (Region definitions context.sigs))
    {leftChildren : List left.RegionId}
    {rightChildren : List right.RegionId}
    (forwardChildren :
      ∀ child, child ∈ leftChildren →
        iso.regions child ∈ rightChildren)
    (backwardChildren :
      ∀ child, child ∈ rightChildren →
        iso.regions.symm child ∈ leftChildren)
    (recurseDenotation :
      ∀ child, child ∈ leftChildren → ∀ leftBody,
        leftRecurse child leftContext = some leftBody →
        ∃ rightBody,
          rightRecurse (iso.regions child) rightContext = some rightBody ∧
          (denoteRegion pre definitionEnv leftEnv leftBody ↔
            denoteRegion pre definitionEnv rightEnv rightBody))
    {leftItems : ItemSeq definitions leftContext.sigs}
    {rightItems : ItemSeq definitions rightContext.sigs}
    (leftCompiled :
      compileChildrenWith? definitions left leftRecurse leftContext
        leftChildren = some leftItems)
    (rightCompiled :
      compileChildrenWith? definitions right rightRecurse rightContext
        rightChildren = some rightItems) :
    denoteItemSeq pre definitionEnv leftEnv leftItems ↔
      denoteItemSeq pre definitionEnv rightEnv rightItems := by
  rw [ItemSeq.denote_iff_mem, ItemSeq.denote_iff_mem]
  constructor
  · intro leftDenotes rightItem rightMember
    obtain ⟨rightChild, rightBody, rightChildMember, rightBodyCompiled,
        rightItemEquality⟩ :=
      compileChildrenWith?_child_for_item definitions right rightRecurse
        rightContext rightCompiled rightItem rightMember
    let leftChild := iso.regions.symm rightChild
    have leftChildMember : leftChild ∈ leftChildren :=
      backwardChildren rightChild rightChildMember
    obtain ⟨leftBody, leftItemMember, leftBodyCompiled⟩ :=
      compileChildrenWith?_item_for_child definitions left leftRecurse
        leftContext leftCompiled leftChild leftChildMember
    obtain ⟨mappedBody, mappedCompiled, bodyDenotation⟩ :=
      recurseDenotation leftChild leftChildMember leftBody leftBodyCompiled
    have mappedChild : iso.regions leftChild = rightChild :=
      iso.regions.right_inv rightChild
    have mappedBodyEquality : mappedBody = rightBody := by
      apply Option.some.inj
      rw [mappedChild] at mappedCompiled
      exact mappedCompiled.symm.trans rightBodyCompiled
    subst mappedBody
    subst rightItem
    exact fun rightBodyDenotes =>
      leftDenotes (.cut leftBody) leftItemMember
        (bodyDenotation.mpr rightBodyDenotes)
  · intro rightDenotes leftItem leftMember
    obtain ⟨leftChild, leftBody, leftChildMember, leftBodyCompiled,
        leftItemEquality⟩ :=
      compileChildrenWith?_child_for_item definitions left leftRecurse
        leftContext leftCompiled leftItem leftMember
    obtain ⟨rightBody, rightBodyCompiled, bodyDenotation⟩ :=
      recurseDenotation leftChild leftChildMember leftBody leftBodyCompiled
    have rightChildMember : iso.regions leftChild ∈ rightChildren :=
      forwardChildren leftChild leftChildMember
    obtain ⟨storedBody, storedMember, storedCompiled⟩ :=
      compileChildrenWith?_item_for_child definitions right rightRecurse
        rightContext rightCompiled (iso.regions leftChild) rightChildMember
    have storedEquality : storedBody = rightBody := by
      exact Option.some.inj (storedCompiled.symm.trans rightBodyCompiled)
    subst storedBody
    subst leftItem
    exact fun leftBodyDenotes =>
      rightDenotes (.cut rightBody) storedMember
        (bodyDenotation.mp leftBodyDenotes)

private theorem climb_succ_root_none
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) (steps : Nat) :
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
  | succ left ih =>
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
          | sheet => simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              have leftParent :
                  diagram.climb left parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using leftClimb
              have rightParent :
                  diagram.climb right parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using rightClimb
              exact congrArg Nat.succ (ih leftParent rightParent)

private theorem climb_to_root_le_count
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {steps : Nat}
    (climbed : diagram.climb steps region = some diagram.root) :
    steps ≤ diagram.regionCount := by
  have reachesCheck := wellFormed.all_regions_reach_root
  unfold ConcreteDiagram.AllRegionsReachRoot at reachesCheck
  have reachesBool := (List.all_eq_true.mp reachesCheck) region
    (Data.Finite.mem_allFin region)
  have reaches : diagram.Encloses diagram.root region :=
    of_decide_eq_true reachesBool
  rcases (encloses_iff_exists diagram diagram.root region).mp reaches with
    ⟨bounded, boundedClimb⟩
  have equal := climb_to_root_unique definitions diagram wellFormed
    climbed boundedClimb
  rw [equal]
  exact Nat.le_of_lt_succ bounded.isLt

/-- A direct child is exactly one compiler-depth step below its parent.
Exposed for construction-owned recursive receipts that must follow the same
region-tree descent as elaboration. -/
theorem child_depth
    (diagram : ConcreteDiagram definitionCount)
    (child parent : diagram.RegionId) (depth : Nat)
    (childData : diagram.regions child = .cut parent)
    (parentDepth : diagram.climb depth parent = some diagram.root) :
    diagram.climb (depth + 1) child = some diagram.root := by
  simpa [ConcreteDiagram.climb, childData] using parentDepth

private theorem climb_positive_ne_self
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId} {steps : Nat} (positive : 0 < steps) :
    diagram.climb steps region ≠ some region := by
  intro loop
  have reachesCheck := wellFormed.all_regions_reach_root
  unfold ConcreteDiagram.AllRegionsReachRoot at reachesCheck
  have reaches : diagram.Encloses diagram.root region :=
    of_decide_eq_true ((List.all_eq_true.mp reachesCheck) region
      (Data.Finite.mem_allFin region))
  obtain ⟨depth, depthClimb⟩ :=
    (encloses_iff_exists diagram diagram.root region).mp reaches
  have combined :
      diagram.climb (steps + depth) region = some diagram.root := by
    rw [ConcreteDiagram.climb_add, loop]
    exact depthClimb
  have unique := climb_to_root_unique definitions diagram wellFormed
    combined depthClimb
  omega

def ContextAbove
    (diagram : ConcreteDiagram definitionCount)
    (context : WireContext diagram) (region : diagram.RegionId) : Prop :=
  context.ids.Nodup ∧
    ∀ wire, wire ∈ context.ids →
      ∃ steps, 0 < steps ∧
        diagram.climb steps region = some (diagram.wires wire).scope

private theorem wiresAt_nodup
    (diagram : ConcreteDiagram definitionCount)
    (region : diagram.RegionId) :
    (diagram.wiresAt region).Nodup :=
  Data.Finite.allFin_nodup diagram.wireCount |>.filter _

private theorem scope_of_mem_wiresAt
    (diagram : ConcreteDiagram definitionCount)
    {region : diagram.RegionId} {wire : diagram.WireId}
    (member : wire ∈ diagram.wiresAt region) :
    (diagram.wires wire).scope = region := by
  unfold ConcreteDiagram.wiresAt at member
  exact eq_of_beq (List.mem_filter.mp member).2

theorem extend_nodup
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram) (region : diagram.RegionId)
    (above : ContextAbove diagram context region) :
    (context.extend region).ids.Nodup := by
  rw [WireContext.extend, List.nodup_append]
  refine ⟨wiresAt_nodup diagram region, above.1, ?_⟩
  intro wire localMember outerWire outerMember equality
  subst outerWire
  have localScope := scope_of_mem_wiresAt diagram localMember
  obtain ⟨steps, positive, climbed⟩ := above.2 wire outerMember
  exact climb_positive_ne_self definitions diagram wellFormed positive
    (by simpa [localScope] using climbed)

theorem extend_above_child
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : WireContext diagram) (parent child : diagram.RegionId)
    (above : ContextAbove diagram context parent)
    (childData : diagram.regions child = .cut parent) :
    ContextAbove diagram (context.extend parent) child := by
  refine ⟨extend_nodup definitions diagram wellFormed context parent above, ?_⟩
  intro wire member
  simp only [WireContext.extend, List.mem_append] at member
  rcases member with localMember | outerMember
  · have scope := scope_of_mem_wiresAt diagram localMember
    exact ⟨1, by omega, by
      simp [ConcreteDiagram.climb, childData, scope]⟩
  · obtain ⟨steps, positive, climbed⟩ := above.2 wire outerMember
    exact ⟨steps + 1, by omega, by
      simpa [ConcreteDiagram.climb, childData] using climbed⟩

private theorem compileRegion?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {fuel depth : Nat} {region : diagram.RegionId}
    {context : WireContext diagram}
    (depthClimb : diagram.climb depth region = some diagram.root)
    (fuelEquation : depth + fuel = diagram.regionCount + 1)
    (coverage : (context.extend region).Covers region) :
    ∃ body,
      compileRegion? definitions diagram fuel region context = some body := by
  induction fuel generalizing depth region context with
  | zero =>
      have bounded := climb_to_root_le_count definitions diagram wellFormed
        depthClimb
      exfalso
      omega
  | succ fuel ih =>
      let extended := context.extend region
      obtain ⟨nodes, nodesCompiled⟩ :=
        compileNodes?_complete definitions diagram wellFormed extended region
          coverage (diagram.nodesAt region) (by
            intro node member
            exact mem_nodesAt diagram region node member)
      obtain ⟨children, childrenCompiled⟩ :=
        compileChildrenWith?_complete definitions diagram
          (compileRegion? definitions diagram fuel) extended
          (diagram.childrenOf region) (by
            intro child member
            have childData := mem_childrenOf diagram region child member
            have nextDepth := child_depth diagram child region depth
              childData depthClimb
            have nextFuel : depth + 1 + fuel = diagram.regionCount + 1 := by
              omega
            have childCoverage := WireContext.extend_covers_child diagram
              extended region child coverage childData
            exact ih nextDepth nextFuel childCoverage)
      refine ⟨finishRegion diagram context region
        (.mk (nodes.append children)), ?_⟩
      simp only [compileRegion?]
      change (compileNodes? definitions diagram extended
        (diagram.nodesAt region)).bind (fun compiledNodes =>
          (compileChildrenWith? definitions diagram
            (compileRegion? definitions diagram fuel) extended
            (diagram.childrenOf region)).bind (fun compiledChildren =>
              some (finishRegion diagram context region
                (.mk (compiledNodes.append compiledChildren))))) =
        some (finishRegion diagram context region
          (.mk (nodes.append children)))
      rw [nodesCompiled, childrenCompiled]
      rfl

private theorem compileRoot?_complete
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) :
    ∃ body, compileRoot? definitions diagram = some body := by
  unfold compileRoot?
  have complete := compileRegion?_complete definitions diagram wellFormed
    (fuel := diagram.regionCount + 1) (depth := 0)
    (region := diagram.root) (context := WireContext.empty diagram)
    (by rfl) (by omega)
    (WireContext.extend_covers_root definitions diagram wellFormed)
  simpa using complete

end ConcreteElaboration

/--
Elaborate one raw graph with a well-formedness witness. The computed value is
the proof-independent private kernel result; the witness only proves `none`
unreachable.
-/
def elaborateWith (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) :
    Region definitions [] :=
  (ConcreteElaboration.compileRoot? definitions diagram).get (by
    obtain ⟨body, compiled⟩ :=
      ConcreteElaboration.compileRoot?_complete definitions diagram wellFormed
    simp [compiled])

theorem elaborateWith_compiles
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions) :
    ConcreteElaboration.compileRoot? definitions diagram =
      some (elaborateWith definitions diagram wellFormed) := by
  obtain ⟨body, compiled⟩ :=
    ConcreteElaboration.compileRoot?_complete definitions diagram wellFormed
  rw [compiled]
  congr 1
  unfold elaborateWith
  simp [compiled]

/-- Total checked elaboration is the only public concrete-to-intrinsic path. -/
def elaborate (checked : CheckedDiagram definitions) :
    Region definitions [] :=
  elaborateWith definitions checked.val checked.property

theorem elaborate_proof_irrelevant
    (left right : diagram.WellFormed definitions) :
    elaborateWith definitions diagram left =
      elaborateWith definitions diagram right := by
  rfl

/-- Checked concrete denotation is the denotation of its unique compiler result. -/
def denoteChecked (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (checked : CheckedDiagram definitions) : Prop :=
  ∃ body,
    ConcreteElaboration.compileRoot? definitions checked.val = some body ∧
      denoteRegion pre definitionEnv Env.empty body

theorem elaborate_denotes_checked
    (checked : CheckedDiagram definitions) :
    denoteChecked pre definitionEnv checked =
      denoteRegion pre definitionEnv Env.empty (elaborate checked) :=
  propext ⟨by
    rintro ⟨body, compiled, denotes⟩
    have elaborated :=
      elaborateWith_compiles definitions checked.val checked.property
    have bodyEquality : body = elaborate checked :=
      Option.some.inj (compiled.symm.trans elaborated)
    simpa [bodyEquality] using denotes,
  fun denotes =>
    ⟨elaborate checked,
      elaborateWith_compiles definitions checked.val checked.property,
      denotes⟩⟩

end VisualProof
