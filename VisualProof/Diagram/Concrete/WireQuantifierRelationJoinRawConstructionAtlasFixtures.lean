import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinRawWireOrigins

namespace VisualProof
namespace ConcreteWireQuantifier
namespace RelationJoinConstructionAtlasFixtures

private def idx {bound : Nat}
    (value : Nat) (valid : value < bound := by native_decide) : Fin bound :=
  ⟨value, valid⟩

private def contentRaw : OpenConcreteDiagram 0 where
  diagram :=
    { regionCount := 2
      nodeCount := 1
      wireCount := 2
      root := 0
      regions
        | ⟨0, _⟩ => .sheet
        | ⟨1, _⟩ => .cut 0
      nodes := fun _ => .atom 1 []
      wires
        | ⟨0, _⟩ =>
            { sig := .iota
              scope := 0
              endpoints := [] }
        | ⟨1, _⟩ =>
            { sig := .rel []
              scope := 1
              endpoints := [⟨0, .head⟩] } }
  boundary := [0, 0]

private theorem contentRaw_wellFormed : contentRaw.WellFormed [] := by
  constructor <;> native_decide

private def content : CheckedOpenDiagram [] :=
  ⟨contentRaw, contentRaw_wellFormed⟩

private def sourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 4
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes
    | ⟨0, _⟩ => .atom 1 [.iota, .iota]
    | ⟨1, _⟩ => .atom 1 []
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota, .iota]
          scope := 1
          endpoints := [⟨0, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .arg 1⟩] }
    | ⟨3, _⟩ =>
        { sig := .rel []
          scope := 1
          endpoints := [⟨1, .head⟩] }

private theorem sourceRaw_wellFormed : sourceRaw.WellFormed [] := by
  native_decide

private def source : CheckedDiagram [] :=
  ⟨sourceRaw, sourceRaw_wellFormed⟩

private def nilAtlas : CertifiedAtlas (source := source) (dying := idx 0)
    (content := content) [] source :=
  initialAtlas

/-- The nil constructor is the exact source enumeration and its constructive
locators return those same dense targets. -/
def nilConforms : Bool :=
  ((Data.Finite.allFin source.val.regionCount).all fun target =>
      decide (nilAtlas.rows.regionAt target = .inl target) &&
      decide ((nilAtlas.locateRegion (.inl target)).1 = target)) &&
    ((Data.Finite.allFin source.val.nodeCount).all fun target =>
      decide (nilAtlas.rows.nodeAt target = .inl target) &&
      decide ((nilAtlas.locateNode (.inl target) (by
        simp [PrefixNodeLive])).1 = target))

example : nilConforms = true := by
  native_decide

private def accepted : RelationJoinResult source (idx 0) content [] :=
  (joinRelation source (idx 0) content []).toOption.get
    (by native_decide)

private def regionCode : PrefixRegionOrigin (source := source)
    (dying := idx 0) (content := content) accepted.steps → Nat × Nat
  | .inl region => (0, region.val)
  | .inr occurrence => (occurrence.1.val + 1, occurrence.2.1.val)

private def nodeCode : PrefixNodeOrigin (source := source)
    (dying := idx 0) (content := content) accepted.steps → Nat × Nat
  | .inl node => (0, node.val)
  | .inr occurrence =>
      match occurrence.2 with
      | .inl node => (occurrence.1.val + 1, node.val)
      | .inr request => (occurrence.1.val + 2, request.val)

private def sourceRegionTarget : Nat :=
  (accepted.constructionAtlas.locateRegion (.inl (idx 0))).1.val

private def freshRegionTarget : Nat :=
  (accepted.constructionAtlas.locateRegion
    (.inr ⟨idx 0, ⟨idx 1, by native_decide⟩⟩)).1.val

private theorem retainedNodeLive :
    PrefixNodeLive (steps := accepted.steps) (.inl (idx 1)) := by
  unfold PrefixNodeLive
  native_decide

private def retainedNodeTarget : Nat :=
  (accepted.constructionAtlas.locateNode
    (.inl (idx 1)) retainedNodeLive).1.val

private def contentNodeTarget : Nat :=
  (accepted.constructionAtlas.locateNode
    (.inr ⟨idx 0, .inl (idx 0)⟩) (by simp [PrefixNodeLive])).1.val

private def requestNodeTarget : Nat :=
  (accepted.constructionAtlas.locateNode
    (.inr ⟨idx 0, .inr (idx 0)⟩) (by simp [PrefixNodeLive])).1.val

private def consumedRejected : Bool :=
  decide ((idx 0 : source.val.NodeId) ∈
    accepted.steps.map RelationJoinStep.application)

/-- Native evidence for the exact executor-owned atlas: ordered retained/fresh
region rows, retained/content/request node rows, constructive inverse locators,
and rejection of the consumed application node. -/
def summary : List (Nat × Nat) × List (Nat × Nat) ×
    List Nat × Bool :=
  (accepted.constructionAtlas.rows.regionRows.map regionCode,
    accepted.constructionAtlas.rows.nodeRows.map nodeCode,
    [sourceRegionTarget, freshRegionTarget, retainedNodeTarget,
      contentNodeTarget, requestNodeTarget],
    consumedRejected)

example : summary =
    ([(0, 0), (0, 1), (1, 1)],
      [(0, 1), (1, 0), (2, 0)], [0, 2, 0, 1, 2], true) := by
  native_decide

private def multiSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 2
  wireCount := 3
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 [.iota, .iota]
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota, .iota]
          scope := 1
          endpoints := [⟨0, .head⟩, ⟨1, .head⟩] }
    | ⟨1, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .arg 0⟩, ⟨1, .arg 0⟩] }
    | ⟨2, _⟩ =>
        { sig := .iota
          scope := 1
          endpoints := [⟨0, .arg 1⟩, ⟨1, .arg 1⟩] }

private theorem multiSourceRaw_wellFormed : multiSourceRaw.WellFormed [] := by
  native_decide

private def multiSource : CheckedDiagram [] :=
  ⟨multiSourceRaw, multiSourceRaw_wellFormed⟩

private def multiAccepted : RelationJoinResult multiSource (idx 0) content [] :=
  (joinRelation multiSource (idx 0) content []).toOption.get
    (by native_decide)

/-- A two-snoc execution checks the atlas-derived operational images and both
terminal equivalence directions over every concrete final carrier. -/
def multiSnocConforms : Bool :=
  decide (multiAccepted.steps.length = 2) &&
    ((Data.Finite.allFin multiSource.val.regionCount).all fun region =>
      decide (multiAccepted.constructionAtlas.regionImage region =
        multiAccepted.boundRegionImage region)) &&
    ((Data.Finite.allFin multiSource.val.nodeCount).all fun node =>
      decide (multiAccepted.constructionAtlas.nodeImage node =
        multiAccepted.boundNodeImage node)) &&
    ((Data.Finite.allFin multiAccepted.plainFinal.val.regionCount).all
      fun target =>
        decide (multiAccepted.finalRegionOriginEquiv.invFun
          (multiAccepted.finalRegionOriginEquiv target) = target)) &&
    ((Data.Finite.allFin multiAccepted.plainFinal.val.nodeCount).all
      fun target =>
        decide (multiAccepted.finalNodeOriginEquiv.invFun
          (multiAccepted.finalNodeOriginEquiv target) = target)) &&
    (multiAccepted.constructionAtlas.rows.regionRows.all fun origin =>
      decide (multiAccepted.finalRegionOriginEquiv
        (multiAccepted.finalRegionOriginEquiv.invFun origin) = origin)) &&
    ((Data.Finite.allFin multiAccepted.boundFinal.val.nodeCount).all fun target =>
      let origin : RelationJoinResult.FinalNodeOrigin multiAccepted :=
        ⟨multiAccepted.constructionAtlas.rows.nodeAt target,
          multiAccepted.constructionAtlas.nodeRowsLive target⟩
      decide (multiAccepted.finalNodeOriginEquiv
        (multiAccepted.finalNodeOriginEquiv.invFun origin) = origin))

example : multiSnocConforms = true := by
  native_decide

private def zeroSourceRaw : ConcreteDiagram 0 where
  regionCount := 2
  nodeCount := 1
  wireCount := 2
  root := 0
  regions
    | ⟨0, _⟩ => .sheet
    | ⟨1, _⟩ => .cut 0
  nodes := fun _ => .atom 1 []
  wires
    | ⟨0, _⟩ =>
        { sig := .rel [.iota, .iota]
          scope := 1
          endpoints := [] }
    | ⟨1, _⟩ =>
        { sig := .rel []
          scope := 1
          endpoints := [⟨0, .head⟩] }

private theorem zeroSourceRaw_wellFormed : zeroSourceRaw.WellFormed [] := by
  native_decide

private def zeroSource : CheckedDiagram [] :=
  ⟨zeroSourceRaw, zeroSourceRaw_wellFormed⟩

private def zeroAccepted : RelationJoinResult zeroSource (idx 0) content [] :=
  (joinRelation zeroSource (idx 0) content []).toOption.get
    (by native_decide)

private def constructionWireCode
    {definitions : List (List Sig)}
    {diagram : CheckedDiagram definitions}
    {dyingWire : diagram.val.WireId}
    {openContent : CheckedOpenDiagram definitions} :
    {steps : List (RelationJoinStep diagram dyingWire openContent)} →
      ConstructionWireOrigin steps → Nat × Nat
  | _, .head position => (0, position.val)
  | _, .tail origin =>
      let code := constructionWireCode origin
      (code.1 + 1, code.2)

private def finalWireCode
    {definitions : List (List Sig)}
    {diagram : CheckedDiagram definitions}
    {dyingWire : diagram.val.WireId}
    {openContent : CheckedOpenDiagram definitions}
    {parameters : List diagram.val.WireId}
    {result : RelationJoinResult diagram dyingWire openContent parameters} :
    FinalWireOrigin result → Nat × Nat
  | .inl wire => (0, wire.1.val)
  | .inr internal =>
      let code := constructionWireCode internal
      (code.1 + 1, code.2)

/-- The terminal wire rows cover both surviving source wires and every
occurrence-indexed internal content wire, with constructive inverse laws in
both directions for singleton and multi-occurrence joins. -/
def terminalWireOriginsConform : Bool :=
  decide (zeroAccepted.steps = []) &&
    decide ((finalWireOriginRows zeroAccepted).map
      (finalWireCode (result := zeroAccepted)) =
      [(0, 1)]) &&
    decide ((finalWireOriginRows accepted).map
      (finalWireCode (result := accepted)) =
      [(0, 1), (0, 2), (0, 3), (1, 0)]) &&
    decide ((finalWireOriginRows multiAccepted).map
      (finalWireCode (result := multiAccepted)) =
      [(0, 1), (0, 2), (1, 0), (2, 0)]) &&
    ((Data.Finite.allFin accepted.plainFinal.val.wireCount).all fun target =>
      decide ((finalWireOriginEquiv accepted).invFun
        (finalWireOriginEquiv accepted target) = target)) &&
    ((finalWireOriginRows accepted).all fun origin =>
      decide (finalWireOriginEquiv accepted
        ((finalWireOriginEquiv accepted).invFun origin) = origin)) &&
    decide ((finalWireOriginRows accepted).length =
      accepted.plainFinal.val.wireCount) &&
    ((Data.Finite.allFin multiAccepted.plainFinal.val.wireCount).all
      fun target =>
        decide ((finalWireOriginEquiv multiAccepted).invFun
          (finalWireOriginEquiv multiAccepted target) = target)) &&
    ((finalWireOriginRows multiAccepted).all fun origin =>
      decide (finalWireOriginEquiv multiAccepted
        ((finalWireOriginEquiv multiAccepted).invFun origin) = origin)) &&
    decide ((finalWireOriginRows multiAccepted).length =
      multiAccepted.plainFinal.val.wireCount)

example : terminalWireOriginsConform = true := by
  native_decide

end RelationJoinConstructionAtlasFixtures
end ConcreteWireQuantifier
end VisualProof
