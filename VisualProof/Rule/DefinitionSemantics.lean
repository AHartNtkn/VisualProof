import VisualProof.Rule.Definition

namespace VisualProof
namespace ConcreteDefinitionWeakening

def embedding (newArgs : List Sig) :
    DefinitionRenaming definitions (newArgs :: definitions) :=
  fun {_} reference => .there reference

theorem get_succ
    (definitions : List (List Sig)) (newArgs : List Sig)
    (definition : Fin definitions.length) :
    (newArgs :: definitions).get definition.succ =
      definitions.get definition := by
  simp

theorem definitionVarAt_succ
    (definitions : List (List Sig)) (newArgs : List Sig)
    (definition : Fin definitions.length) :
    ConcreteElaboration.Internal.definitionVarAt
        (newArgs :: definitions) definition.succ =
      .there
        (ConcreteElaboration.Internal.definitionVarAt definitions definition) := by
  cases definitions with
  | nil => exact nomatch definition
  | cons head tail =>
      cases definition using Fin.cases with
      | zero => rfl
      | succ earlier => rfl

def context {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (sourceContext : ConcreteElaboration.WireContext source) :
    ConcreteElaboration.WireContext
      (diagram (newArgs := newArgs) source) :=
  ⟨sourceContext.ids⟩

@[simp] theorem endpointOwner?_diagram
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (endpoint : CEndpoint source.nodeCount) :
    (diagram (definitions := definitions) (newArgs := newArgs) source).endpointOwner?
        endpoint = source.endpointOwner? endpoint := by
  rfl

@[simp] theorem resolveWireIn?_diagram
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (ids : List source.WireId)
    (wire : source.WireId) :
    ConcreteElaboration.Internal.resolveWireIn?
        (diagram (definitions := definitions) (newArgs := newArgs) source)
        ids wire =
      ConcreteElaboration.Internal.resolveWireIn? source ids wire := by
  unfold diagram
  induction ids with
  | nil => rfl
  | cons head tail induction =>
      by_cases same : wire = head
      · simp [ConcreteElaboration.Internal.resolveWireIn?, same]
      · simp [ConcreteElaboration.Internal.resolveWireIn?, same, induction]

@[simp] theorem resolveWire?_diagram
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (sourceContext : ConcreteElaboration.WireContext source)
    (wire : source.WireId) :
    ConcreteElaboration.Internal.resolveWire?
        (diagram (definitions := definitions) (newArgs := newArgs) source)
        (context (definitions := definitions) (newArgs := newArgs)
          source sourceContext) wire =
      ConcreteElaboration.Internal.resolveWire? source sourceContext wire := by
  exact resolveWireIn?_diagram source sourceContext.ids wire

@[simp] theorem resolveExpected?_diagram
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (sourceContext : ConcreteElaboration.WireContext source)
    (wire : source.WireId) (expected : Sig) :
    ConcreteElaboration.Internal.resolveExpected?
        (diagram (definitions := definitions) (newArgs := newArgs) source)
        (context (definitions := definitions) (newArgs := newArgs)
          source sourceContext) wire expected =
      ConcreteElaboration.Internal.resolveExpected?
        source sourceContext wire expected := by
  unfold ConcreteElaboration.Internal.resolveExpected?
  by_cases same : (source.wires wire).sig = expected
  · simp only [dif_pos same, resolveWire?_diagram]
    rfl
  · simp only [dif_neg same]
    rfl

@[simp] theorem resolvePort?_diagram
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (sourceContext : ConcreteElaboration.WireContext source)
    (sourceNode : source.NodeId) (port : CPort) (expected : Sig) :
    ConcreteElaboration.Internal.resolvePort?
        (diagram (definitions := definitions) (newArgs := newArgs) source)
        (context (definitions := definitions) (newArgs := newArgs)
          source sourceContext) sourceNode port expected =
      ConcreteElaboration.Internal.resolvePort?
        source sourceContext sourceNode port expected := by
  unfold ConcreteElaboration.Internal.resolvePort?
  rw [endpointOwner?_diagram]
  congr 1
  funext wire
  exact resolveExpected?_diagram source sourceContext wire expected

@[simp] theorem resolveArgs?_diagram
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (sourceContext : ConcreteElaboration.WireContext source)
    (sourceNode : source.NodeId) (args : List Sig) (start : Nat) :
    ConcreteElaboration.Internal.resolveArgs?
        (diagram (definitions := definitions) (newArgs := newArgs) source)
        (context (definitions := definitions) (newArgs := newArgs)
          source sourceContext) sourceNode args start =
      ConcreteElaboration.Internal.resolveArgs?
        source sourceContext sourceNode args start := by
  induction args generalizing start with
  | nil => rfl
  | cons head tail induction =>
      simp only [ConcreteElaboration.Internal.resolveArgs?]
      rw [resolvePort?_diagram, induction]
      cases resolvedHead : ConcreteElaboration.Internal.resolvePort?
          source sourceContext sourceNode (.arg start) head with
      | none => rfl
      | some resolvedHead =>
          cases resolvedTail : ConcreteElaboration.Internal.resolveArgs?
              source sourceContext sourceNode tail (start + 1) <;> rfl

@[simp] theorem resolveIdentityPorts?_diagram
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (sourceContext : ConcreteElaboration.WireContext source)
    (sourceNode : source.NodeId) (sig : Sig) (arity start : Nat) :
    ConcreteElaboration.Internal.resolveIdentityPorts?
        (diagram (definitions := definitions) (newArgs := newArgs) source)
        (context (definitions := definitions) (newArgs := newArgs)
          source sourceContext) sourceNode sig arity start =
      ConcreteElaboration.Internal.resolveIdentityPorts?
        source sourceContext sourceNode sig arity start := by
  induction arity generalizing start with
  | zero => rfl
  | succ arity induction =>
      simp only [ConcreteElaboration.Internal.resolveIdentityPorts?]
      rw [resolvePort?_diagram, induction]
      cases resolvedHead : ConcreteElaboration.Internal.resolvePort?
          source sourceContext sourceNode (.identity start) sig with
      | none => rfl
      | some resolvedHead =>
          cases resolvedTail : ConcreteElaboration.Internal.resolveIdentityPorts?
              source sourceContext sourceNode sig arity (start + 1) <;> rfl

theorem compileNode?_weaken
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (sourceContext : ConcreteElaboration.WireContext source)
    (sourceNode : source.NodeId) :
    ConcreteElaboration.Internal.compileNode?
        (newArgs :: definitions)
        (diagram (definitions := definitions) (newArgs := newArgs) source)
        (context (definitions := definitions) (newArgs := newArgs)
          source sourceContext) sourceNode =
      (ConcreteElaboration.Internal.compileNode? definitions source
        sourceContext sourceNode).map
        (Item.renameDefinitions (embedding (definitions := definitions) newArgs)) := by
  rw [ConcreteElaboration.Internal.compileNode?_equation,
    ConcreteElaboration.Internal.compileNode?_equation]
  cases nodeData : source.nodes sourceNode with
  | atom region args =>
      rw [show (diagram (newArgs := newArgs) source).nodes sourceNode =
        node (source.nodes sourceNode) from rfl, nodeData]
      simp only [node]
      rw [resolvePort?_diagram, resolveArgs?_diagram]
      cases resolvedHead : ConcreteElaboration.Internal.resolvePort?
          source sourceContext sourceNode .head (.rel args) with
      | none => rfl
      | some resolvedHead =>
          cases resolvedArgs : ConcreteElaboration.Internal.resolveArgs?
              source sourceContext sourceNode args 0 <;> rfl
  | ref region definition args =>
      rw [show (diagram (newArgs := newArgs) source).nodes sourceNode =
        node (source.nodes sourceNode) from rfl, nodeData]
      simp only [node, get_succ]
      rw [resolveArgs?_diagram]
      by_cases signature : definitions.get definition = args
      · subst args
        simp only [dif_pos rfl]
        cases resolvedArgs : ConcreteElaboration.Internal.resolveArgs?
            source sourceContext sourceNode (definitions.get definition) 0 with
        | none => rfl
        | some resolvedArgs =>
            rw [definitionVarAt_succ]
            rfl
      · simp only [dif_neg signature, Option.map_none]
        rfl
  | identity region sig arity =>
      rw [show (diagram (newArgs := newArgs) source).nodes sourceNode =
        node (source.nodes sourceNode) from rfl, nodeData]
      simp only [node]
      rw [resolveIdentityPorts?_diagram]
      by_cases arityWitness : 2 ≤ arity
      · simp only [dif_pos arityWitness]
        cases resolvedPorts : ConcreteElaboration.Internal.resolveIdentityPorts?
            source sourceContext sourceNode sig arity 0 with
        | none => rfl
        | some resolvedPorts => rfl
      · simp only [dif_neg arityWitness, Option.map_none]
        rfl

@[simp] theorem nodesAt_diagram
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (region : source.RegionId) :
    (diagram (newArgs := newArgs) source).nodesAt region =
      source.nodesAt region := by
  unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList diagram
  apply List.filter_congr
  intro sourceNode sourceNodeMember
  change ((node (source.nodes sourceNode)).region == region) =
    ((source.nodes sourceNode).region == region)
  cases source.nodes sourceNode <;> rfl

@[simp] theorem childrenOf_diagram
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (region : source.RegionId) :
    (diagram (newArgs := newArgs) source).childrenOf region =
      source.childrenOf region := by
  unfold ConcreteDiagram.childrenOf ConcreteDiagram.regionsList
  apply List.filter_congr
  intro child childMember
  cases regionData : source.regions child with
  | sheet => simp [diagram, regionData]
  | cut parent =>
      rcases parent with ⟨parentValue, parentBound⟩
      rcases region with ⟨regionValue, regionBound⟩
      simp only [diagram, regionData]

@[simp] theorem ItemSeq.renameDefinitions_append
    (rho : DefinitionRenaming sourceDefinitions targetDefinitions)
    (right : ItemSeq sourceDefinitions wireContext) :
    (left : ItemSeq sourceDefinitions wireContext) →
    (left.append right).renameDefinitions rho =
      (left.renameDefinitions rho).append (right.renameDefinitions rho)
  | .nil => rfl
  | .cons head tail => by
      simp only [ItemSeq.append, ItemSeq.renameDefinitions]
      rw [ItemSeq.renameDefinitions_append rho right tail]

theorem compileNodes?_weaken
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (sourceContext : ConcreteElaboration.WireContext source)
    (sourceNodes : List source.NodeId) :
    ConcreteElaboration.compileNodes?
        (newArgs :: definitions)
        (diagram (newArgs := newArgs) source)
        (context (newArgs := newArgs) source sourceContext) sourceNodes =
      (ConcreteElaboration.compileNodes? definitions source
        sourceContext sourceNodes).map
        (ItemSeq.renameDefinitions
          (embedding (definitions := definitions) newArgs)) := by
  induction sourceNodes with
  | nil => rfl
  | cons sourceNode tail induction =>
      rw [ConcreteElaboration.compileNodes?_equation,
        ConcreteElaboration.compileNodes?_equation]
      simp only [compileNode?_weaken, induction]
      cases headResult : ConcreteElaboration.Internal.compileNode?
          definitions source sourceContext sourceNode with
      | none => rfl
      | some head =>
          cases tailResult : ConcreteElaboration.compileNodes?
              definitions source sourceContext tail with
          | none => rfl
          | some rest => rfl

theorem compileChildrenWith?_weaken
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length)
    (sourceRecurse : (region : source.RegionId) →
      (sourceContext : ConcreteElaboration.WireContext source) →
      Option (Region definitions sourceContext.sigs))
    (targetRecurse : (region : (diagram (newArgs := newArgs) source).RegionId) →
      (targetContext : ConcreteElaboration.WireContext
        (diagram (newArgs := newArgs) source)) →
      Option (Region (newArgs :: definitions) targetContext.sigs))
    (recurseLaw : ∀ region sourceContext,
      targetRecurse region (context (newArgs := newArgs) source sourceContext) =
        (sourceRecurse region sourceContext).map
          (Region.renameDefinitions
            (embedding (definitions := definitions) newArgs)))
    (sourceContext : ConcreteElaboration.WireContext source) :
    (children : List source.RegionId) →
    ConcreteElaboration.compileChildrenWith?
        (newArgs :: definitions) (diagram (newArgs := newArgs) source)
        targetRecurse (context (newArgs := newArgs) source sourceContext)
        children =
      (ConcreteElaboration.compileChildrenWith? definitions source
        sourceRecurse sourceContext children).map
        (ItemSeq.renameDefinitions
          (embedding (definitions := definitions) newArgs))
  | [] => rfl
  | child :: tail => by
      simp only [ConcreteElaboration.compileChildrenWith?]
      rw [recurseLaw, compileChildrenWith?_weaken source sourceRecurse
        targetRecurse recurseLaw sourceContext tail]
      cases childResult : sourceRecurse child sourceContext with
      | none => rfl
      | some body =>
          cases tailResult : ConcreteElaboration.compileChildrenWith?
              definitions source sourceRecurse sourceContext tail with
          | none => rfl
          | some rest => rfl

theorem compileRegion?_weaken
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : ConcreteDiagram definitions.length) :
    ∀ (fuel : Nat) (region : source.RegionId)
      (sourceContext : ConcreteElaboration.WireContext source),
      ConcreteElaboration.compileRegion?
          (newArgs :: definitions) (diagram (newArgs := newArgs) source)
          fuel region (context (newArgs := newArgs) source sourceContext) =
        (ConcreteElaboration.compileRegion? definitions source fuel region
          sourceContext).map
          (Region.renameDefinitions
            (embedding (definitions := definitions) newArgs)) := by
  intro fuel
  induction fuel with
  | zero => intro region sourceContext; rfl
  | succ fuel induction =>
      intro region sourceContext
      rw [ConcreteElaboration.compileRegion?_succ,
        ConcreteElaboration.compileRegion?_succ]
      dsimp only
      simp only [nodesAt_diagram, childrenOf_diagram]
      have nodesLaw :
          ConcreteElaboration.compileNodes? (newArgs :: definitions)
              (diagram (newArgs := newArgs) source)
              ((context (newArgs := newArgs) source sourceContext).extend region)
              (source.nodesAt region) =
            (ConcreteElaboration.compileNodes? definitions source
              (sourceContext.extend region) (source.nodesAt region)).map
              (ItemSeq.renameDefinitions
                (embedding (definitions := definitions) newArgs)) :=
        compileNodes?_weaken source (sourceContext.extend region)
          (source.nodesAt region)
      rw [nodesLaw]
      have childrenLaw :
          ConcreteElaboration.compileChildrenWith? (newArgs :: definitions)
              (diagram (newArgs := newArgs) source)
              (ConcreteElaboration.compileRegion? (newArgs :: definitions)
                (diagram (newArgs := newArgs) source) fuel)
              ((context (newArgs := newArgs) source sourceContext).extend region)
              (source.childrenOf region) =
            (ConcreteElaboration.compileChildrenWith? definitions source
              (ConcreteElaboration.compileRegion? definitions source fuel)
              (sourceContext.extend region) (source.childrenOf region)).map
              (ItemSeq.renameDefinitions
                (embedding (definitions := definitions) newArgs)) :=
        compileChildrenWith?_weaken source
          (ConcreteElaboration.compileRegion? definitions source fuel)
          (ConcreteElaboration.compileRegion? (newArgs :: definitions)
            (diagram (newArgs := newArgs) source) fuel)
          induction (sourceContext.extend region) (source.childrenOf region)
      rw [childrenLaw]
      cases nodesResult : ConcreteElaboration.compileNodes? definitions source
          (sourceContext.extend region) (source.nodesAt region) with
      | none => rfl
      | some nodes =>
          cases childrenResult : ConcreteElaboration.compileChildrenWith?
              definitions source
              (ConcreteElaboration.compileRegion? definitions source fuel)
              (sourceContext.extend region) (source.childrenOf region) with
          | none => rfl
          | some children =>
              change some
                  (ConcreteElaboration.finishRegion
                    (diagram (newArgs := newArgs) source)
                    (context (newArgs := newArgs) source sourceContext) region
                    (.mk ((nodes.renameDefinitions
                      (embedding (definitions := definitions) newArgs)).append
                      (children.renameDefinitions
                        (embedding (definitions := definitions) newArgs))))) =
                some ((ConcreteElaboration.finishRegion source sourceContext
                  region (.mk (nodes.append children))).renameDefinitions
                    (embedding (definitions := definitions) newArgs))
              rw [← ItemSeq.renameDefinitions_append]
              change some
                  (ConcreteElaboration.finishRegion
                    (diagram (newArgs := newArgs) source)
                    (context (newArgs := newArgs) source sourceContext) region
                    ((Region.mk (nodes.append children)).renameDefinitions
                      (embedding (definitions := definitions) newArgs))) =
                some ((ConcreteElaboration.finishRegion source sourceContext
                  region (Region.mk (nodes.append children))).renameDefinitions
                    (embedding (definitions := definitions) newArgs))
              have finishDiagram :
                  ConcreteElaboration.finishRegion
                      (diagram (newArgs := newArgs) source)
                      (context (newArgs := newArgs) source sourceContext) region
                      ((Region.mk (nodes.append children)).renameDefinitions
                        (embedding (definitions := definitions) newArgs)) =
                    ConcreteElaboration.finishRegion source sourceContext region
                      ((Region.mk (nodes.append children)).renameDefinitions
                        (embedding (definitions := definitions) newArgs)) := by
                rw [ConcreteElaboration.finishRegion_eq_signatures,
                  ConcreteElaboration.finishRegion_eq_signatures]
                rfl
              rw [finishDiagram]
              rw [ConcreteElaboration.finishRegion_renameDefinitions]
              rfl

theorem compileOpenRoot?_weaken
    {definitions : List (List Sig)} {newArgs : List Sig}
    (source : OpenConcreteDiagram definitions.length) :
    ConcreteElaboration.compileOpenRoot? (newArgs :: definitions)
        (openDiagram (newArgs := newArgs) source) =
      (ConcreteElaboration.compileOpenRoot? definitions source).map
        (Region.renameDefinitions
          (embedding (definitions := definitions) newArgs)) := by
  rw [ConcreteElaboration.compileOpenRoot?_equation,
    ConcreteElaboration.compileOpenRoot?_equation]
  dsimp only
  simp only [nodesAt_diagram, childrenOf_diagram]
  let sourceContext : ConcreteElaboration.WireContext source.diagram :=
    ⟨ConcreteElaboration.openRootLocalWires source ++
      ConcreteElaboration.openBoundaryWires source⟩
  have nodesLaw :
      ConcreteElaboration.compileNodes? (newArgs :: definitions)
          (diagram (newArgs := newArgs) source.diagram)
          ⟨ConcreteElaboration.openRootLocalWires
              (openDiagram (newArgs := newArgs) source) ++
            ConcreteElaboration.openBoundaryWires
              (openDiagram (newArgs := newArgs) source)⟩
          (source.diagram.nodesAt source.diagram.root) =
        (ConcreteElaboration.compileNodes? definitions source.diagram
          sourceContext (source.diagram.nodesAt source.diagram.root)).map
          (ItemSeq.renameDefinitions
            (embedding (definitions := definitions) newArgs)) :=
    by
      simpa [sourceContext] using
        compileNodes?_weaken source.diagram sourceContext
          (source.diagram.nodesAt source.diagram.root)
  rw [nodesLaw]
  have childrenLaw :
      ConcreteElaboration.compileChildrenWith? (newArgs :: definitions)
          (diagram (newArgs := newArgs) source.diagram)
          (ConcreteElaboration.compileRegion? (newArgs :: definitions)
            (diagram (newArgs := newArgs) source.diagram)
            source.diagram.regionCount)
          ⟨ConcreteElaboration.openRootLocalWires
              (openDiagram (newArgs := newArgs) source) ++
            ConcreteElaboration.openBoundaryWires
              (openDiagram (newArgs := newArgs) source)⟩
          (source.diagram.childrenOf source.diagram.root) =
        (ConcreteElaboration.compileChildrenWith? definitions source.diagram
          (ConcreteElaboration.compileRegion? definitions source.diagram
            source.diagram.regionCount)
          sourceContext (source.diagram.childrenOf source.diagram.root)).map
          (ItemSeq.renameDefinitions
            (embedding (definitions := definitions) newArgs)) :=
    by
      simpa [sourceContext] using
        compileChildrenWith?_weaken source.diagram
          (ConcreteElaboration.compileRegion? definitions source.diagram
            source.diagram.regionCount)
          (ConcreteElaboration.compileRegion? (newArgs :: definitions)
            (diagram (newArgs := newArgs) source.diagram)
            source.diagram.regionCount)
          (compileRegion?_weaken source.diagram source.diagram.regionCount)
          sourceContext (source.diagram.childrenOf source.diagram.root)
  rw [childrenLaw]
  cases nodesResult : ConcreteElaboration.compileNodes? definitions
      source.diagram sourceContext
      (source.diagram.nodesAt source.diagram.root) with
  | none => rfl
  | some nodes =>
      cases childrenResult : ConcreteElaboration.compileChildrenWith?
          definitions source.diagram
          (ConcreteElaboration.compileRegion? definitions source.diagram
            source.diagram.regionCount)
          sourceContext (source.diagram.childrenOf source.diagram.root) with
      | none => rfl
      | some children =>
          let body : Region definitions
              ((ConcreteElaboration.openRootLocalWires source ++
                ConcreteElaboration.openBoundaryWires source).map
                fun wire => (source.diagram.wires wire).sig) :=
            Region.mk (nodes.append children)
          have targetAppend :=
            ConcreteElaboration.finishOpenRoot_append_renameDefinitions
              (embedding (definitions := definitions) newArgs)
              (openDiagram (newArgs := newArgs) source) nodes children
          have targetSignatures :=
            ConcreteElaboration.finishOpenRoot_eq_signatures
              (openDiagram (newArgs := newArgs) source) body
          have sourceSignatures :=
            ConcreteElaboration.finishOpenRoot_eq_signatures source body
          have sameFinisher := targetSignatures.trans sourceSignatures.symm
          have finalLaw := targetAppend.trans
            (congrArg
              (Region.renameDefinitions
                (embedding (definitions := definitions) newArgs))
              sameFinisher)
          simp only [Option.map_some, Option.bind_some]
          exact congrArg some finalLaw

/-- A checked weakening compiles to the source body with every stored
definition reference shifted through the new chronological entry. -/
theorem compiled_body_eq
    {definitions : List (List Sig)} {newArgs : List Sig}
    {source : CheckedOpenDiagram definitions}
    (weakened : WeakenedDefinitionBody newArgs source)
    (sourceCompiled : OpenCompilation source)
    (targetCompiled : OpenCompilation weakened.body) :
    targetCompiled.body = sourceCompiled.body.renameDefinitions
      (embedding (definitions := definitions) newArgs) := by
  have naturality := compileOpenRoot?_weaken
    (newArgs := newArgs) source.val
  have targetGenerated :
      ConcreteElaboration.compileOpenRoot? (newArgs :: definitions)
          (openDiagram (newArgs := newArgs) source.val) =
        some targetCompiled.body := by
    simpa [WeakenedDefinitionBody.body] using
      targetCompiled.body_generated
  rw [sourceCompiled.body_generated] at naturality
  rw [targetGenerated] at naturality
  simpa using Option.some.inj naturality

/-- Definition weakening does not alter ordered boundary variables. -/
theorem compiled_boundary_eq
    {definitions : List (List Sig)} {newArgs : List Sig}
    {source : CheckedOpenDiagram definitions}
    (weakened : WeakenedDefinitionBody newArgs source)
    (sourceCompiled : OpenCompilation source)
    (targetCompiled : OpenCompilation weakened.body) :
    targetCompiled.boundary = sourceCompiled.boundary := by
  have targetGenerated :
      compileExtractedBoundary? weakened.body =
        some targetCompiled.boundary :=
    targetCompiled.boundary_generated
  have sourceGenerated :
      compileExtractedBoundary? source =
        some sourceCompiled.boundary :=
    sourceCompiled.boundary_generated
  have compilerExact :
      compileExtractedBoundary? weakened.body =
        compileExtractedBoundary? source := by
    simp [compileExtractedBoundary?, WeakenedDefinitionBody.body,
      ConcreteDefinitionWeakening.openDiagram,
      ConcreteDefinitionWeakening.diagram,
      ConcreteElaboration.openBoundaryWires]
  exact Option.some.inj
    (targetGenerated.symm.trans (compilerExact.trans sourceGenerated))

/-- The compiled weakened open body denotes exactly the original compiled
body under the prior definition environment. -/
theorem compiled_open_denotes_iff
    {definitions : List (List Sig)} {newArgs : List Sig}
    {source : CheckedOpenDiagram definitions}
    (weakened : WeakenedDefinitionBody newArgs source)
    (sourceCompiled : OpenCompilation source)
    (targetCompiled : OpenCompilation weakened.body)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre (newArgs :: definitions))
    (values : BoundaryEnv pre (checkedBoundarySigs source)) :
    denoteOpen pre definitionEnv targetCompiled.openDiagram values ↔
      denoteOpen pre (DefinitionEnv.tail definitionEnv)
        sourceCompiled.openDiagram values := by
  unfold denoteOpen OpenCompilation.openDiagram
  have compiledBoundary :=
    compiled_boundary_eq weakened sourceCompiled targetCompiled
  constructor
  · rintro ⟨env, boundaryValues, bodyDenotes⟩
    refine ⟨env, ?_, ?_⟩
    change Vars.denote env sourceCompiled.boundary = values
    simpa [← compiledBoundary] using boundaryValues
    rw [compiled_body_eq weakened sourceCompiled targetCompiled] at bodyDenotes
    exact (denoteRegion_renameDefinitions pre definitionEnv
      (embedding (definitions := definitions) newArgs) env
      sourceCompiled.body).mp bodyDenotes
  · rintro ⟨env, boundaryValues, bodyDenotes⟩
    refine ⟨env, ?_, ?_⟩
    change Vars.denote env targetCompiled.boundary = values
    simpa [compiledBoundary] using boundaryValues
    rw [compiled_body_eq weakened sourceCompiled targetCompiled]
    exact (denoteRegion_renameDefinitions pre definitionEnv
      (embedding (definitions := definitions) newArgs) env
      sourceCompiled.body).mpr bodyDenotes

end ConcreteDefinitionWeakening

namespace CheckedDefinitionData

/-- Resolving a checked stored body preserves the intrinsic meaning of its
typed definition reference in the complete current definition context. -/
theorem resolved_denotes_definitionBody
    {definitions : Definitions}
    (data : CheckedDefinitionData definitions)
    (reference : DefVar definitions.signatures args)
    (resolved : ResolvedDefinitionBody definitions args)
    (accepted : data.resolveBody reference = Except.ok resolved)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions.signatures)
    (values : BoundaryEnv pre (checkedBoundarySigs resolved.body)) :
    denoteOpen pre definitionEnv resolved.compilation.openDiagram values ↔
      definitions.definitionBody pre definitionEnv reference
        (resolved.boundarySignatures ▸ values) := by
  induction data with
  | nil =>
      nomatch reference
  | @snoc prior priorData latestBody latestCompiled induction =>
      cases reference with
      | here =>
          rw [resolveBody_here_eq] at accepted
          cases weakenedAccepted :
              weakenDefinitionBody (checkedBoundarySigs latestBody)
                latestBody with
          | error error =>
              rw [weakenedAccepted] at accepted
              dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                Except.bind, Except.pure, Except.map] at accepted
              contradiction
          | ok weakened =>
              cases compilationAccepted : weakened.compile? with
              | error error =>
                  rw [weakenedAccepted] at accepted
                  dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                    Except.bind, Except.pure, Except.map] at accepted
                  rw [compilationAccepted] at accepted
                  dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                    Except.bind, Except.pure, Except.map] at accepted
                  contradiction
              | ok compilation =>
                  rw [weakenedAccepted] at accepted
                  dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                    Except.bind, Except.pure, Except.map] at accepted
                  rw [compilationAccepted] at accepted
                  dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                    Except.bind, Except.pure, Except.map] at accepted
                  cases accepted
                  simpa [Definitions.definitionBody,
                    DefinitionData.bodyMeaning] using
                    ConcreteDefinitionWeakening.compiled_open_denotes_iff
                      weakened latestCompiled compilation pre definitionEnv
                      values
      | there earlier =>
          rw [resolveBody_there_eq] at accepted
          cases earlierAccepted : priorData.resolveBody earlier with
          | error error =>
              rw [earlierAccepted] at accepted
              dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                Except.bind, Except.pure, Except.map] at accepted
              contradiction
          | ok earlierBody =>
              cases weakenedAccepted :
                  weakenDefinitionBody (checkedBoundarySigs latestBody)
                    earlierBody.body with
              | error error =>
                  rw [earlierAccepted] at accepted
                  dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                    Except.bind, Except.pure, Except.map] at accepted
                  rw [weakenedAccepted] at accepted
                  dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                    Except.bind, Except.pure, Except.map] at accepted
                  contradiction
              | ok weakened =>
                  cases compilationAccepted : weakened.compile? with
                  | error error =>
                      rw [earlierAccepted] at accepted
                      dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                        Except.bind, Except.pure, Except.map] at accepted
                      rw [weakenedAccepted] at accepted
                      dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                        Except.bind, Except.pure, Except.map] at accepted
                      rw [compilationAccepted] at accepted
                      dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                        Except.bind, Except.pure, Except.map] at accepted
                      contradiction
                  | ok compilation =>
                      rw [earlierAccepted] at accepted
                      dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                        Except.bind, Except.pure, Except.map] at accepted
                      rw [weakenedAccepted] at accepted
                      dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                        Except.bind, Except.pure, Except.map] at accepted
                      rw [compilationAccepted] at accepted
                      dsimp [Bind.bind, Monad.toBind, Except.instMonad,
                        Except.bind, Except.pure, Except.map] at accepted
                      cases accepted
                      simpa [Definitions.definitionBody] using
                        (ConcreteDefinitionWeakening.compiled_open_denotes_iff
                          weakened earlierBody.compilation compilation pre
                          definitionEnv values).trans
                          (induction earlier earlierBody earlierAccepted
                            (DefinitionEnv.tail definitionEnv) values)

end CheckedDefinitionData
end VisualProof
