import VisualProof.Diagram.Context
import VisualProof.Diagram.Scope

namespace VisualProof.Diagram

open VisualProof.Theory

namespace DiagramContext

private def ItemSeq.mapFrameInternalWire
    (leading trailing : ItemSeq wires)
    {before after : Region wires}
    (bodyMap : ∀ {signature}, Region.InternalWire before signature →
      Region.InternalWire after signature) :
    ∀ {signature},
      ItemSeq.InternalWire
          (leading.append (.cons (.cut before) trailing)) signature →
        ItemSeq.InternalWire
          (leading.append (.cons (.cut after) trailing)) signature :=
  match leading with
  | .nil => fun wire =>
      match wire with
      | .headCut nested => .headCut (bodyMap nested)
      | .tail nested => .tail nested
  | .cons (.atom _ _) tail => fun wire =>
      match wire with
      | .tail nested => .tail
          (ItemSeq.mapFrameInternalWire tail trailing bodyMap nested)
  | .cons (.identity _ _ _) tail => fun wire =>
      match wire with
      | .tail nested => .tail
          (ItemSeq.mapFrameInternalWire tail trailing bodyMap nested)
  | .cons (.cut _) tail => fun wire =>
      match wire with
      | .headCut nested => .headCut nested
      | .tail nested => .tail
          (ItemSeq.mapFrameInternalWire tail trailing bodyMap nested)

private theorem ItemSeq.ownerPathFrom_mapFrameInternalWire
    (leading trailing : ItemSeq wires)
    {before after : Region wires}
    (bodyMap : ∀ {signature}, Region.InternalWire before signature →
      Region.InternalWire after signature)
    (bodyOwner : ∀ {signature} (wire : Region.InternalWire before signature),
      (bodyMap wire).ownerPath = wire.ownerPath)
    {signature}
    (wire : ItemSeq.InternalWire
      (leading.append (.cons (.cut before) trailing)) signature)
    (itemIndex : Nat) :
    (ItemSeq.mapFrameInternalWire leading trailing bodyMap wire).ownerPathFrom
        itemIndex =
      wire.ownerPathFrom itemIndex := by
  cases leading with
  | nil =>
      cases wire with
      | headCut nested => exact congrArg (List.cons itemIndex) (bodyOwner nested)
      | tail nested => rfl
  | cons head tail =>
      cases head with
      | atom head ports =>
          cases wire with
          | tail nested =>
              exact ItemSeq.ownerPathFrom_mapFrameInternalWire tail trailing
                bodyMap bodyOwner nested (itemIndex + 1)
      | identity signature arity ports =>
          cases wire with
          | tail nested =>
              exact ItemSeq.ownerPathFrom_mapFrameInternalWire tail trailing
                bodyMap bodyOwner nested (itemIndex + 1)
      | cut body =>
          cases wire with
          | headCut nested => rfl
          | tail nested =>
              exact ItemSeq.ownerPathFrom_mapFrameInternalWire tail trailing
                bodyMap bodyOwner nested (itemIndex + 1)

def mapInternalWire :
    (context : DiagramContext outer holeWires) →
    {before after : Region holeWires} →
    (holeMap : ∀ {signature}, Region.InternalWire before signature →
      Region.InternalWire after signature) →
    ∀ {signature}, Region.InternalWire (context.fill before) signature →
      Region.InternalWire (context.fill after) signature
  | .hole, _, _, holeMap => holeMap
  | .cut _ leading trailing child, _, _, holeMap => fun wire =>
      match wire with
      | .here localWire => .here localWire
      | .nested nestedWire =>
          .nested (ItemSeq.mapFrameInternalWire leading trailing
            (child.mapInternalWire holeMap) nestedWire)

theorem ownerPath_mapInternalWire
    (context : DiagramContext outer holeWires)
    {before after : Region holeWires}
    (holeMap : ∀ {signature}, Region.InternalWire before signature →
      Region.InternalWire after signature)
    (holeOwner : ∀ {signature} (wire : Region.InternalWire before signature),
      (holeMap wire).ownerPath = wire.ownerPath)
    {signature}
    (wire : Region.InternalWire (context.fill before) signature) :
    (context.mapInternalWire holeMap wire).ownerPath = wire.ownerPath := by
  cases context with
  | hole => simpa only [mapInternalWire] using holeOwner wire
  | @cut currentOuter currentHole locals leading trailing child =>
      cases wire with
      | here localWire => rfl
      | nested nestedWire =>
          exact ItemSeq.ownerPathFrom_mapFrameInternalWire leading trailing
            (child.mapInternalWire holeMap)
            (fun nested => child.ownerPath_mapInternalWire holeMap holeOwner nested)
            nestedWire 0

theorem holeCanonical
    (context : DiagramContext outer holeWires) (body : Region holeWires)
    (filledCanonical : (context.fill body).Canonical) : body.Canonical := by
  induction context with
  | hole => exact filledCanonical
  | @cut currentOuter currentHole locals leading trailing child induction =>
      have children :=
        (ItemSeq.childrenCanonical_append leading
          (.cons (.cut (child.fill body)) trailing)).mp filledCanonical.2
      exact induction body children.2.1

/-- Replacing a canonical hole body by another canonical body preserves the
whole recursive context exactly when every hole-interface wire preserves
incidence nonemptiness. Unchanged incidences outside the hole combine with
the replacement's nonempty incidence set to preserve both the two-incidence
floor and the DCA. The result also exposes that same boundary fact to the
enclosing caller. -/
theorem replaceCanonical
    (context : DiagramContext outer holeWires)
    (before after : Region holeWires)
    (sourceCanonical : (context.fill before).Canonical)
    (afterCanonical : after.Canonical)
    (holeNonempty : ∀ {signature} (wire : Var holeWires signature),
      before.incidencePaths wire.index.val ≠ [] ↔
        after.incidencePaths wire.index.val ≠ []) :
    (context.fill after).Canonical ∧
      ∀ {signature} (wire : Var outer signature),
        (context.fill before).incidencePaths wire.index.val ≠ [] ↔
          (context.fill after).incidencePaths wire.index.val ≠ [] := by
  induction context with
  | hole => exact ⟨afterCanonical, holeNonempty⟩
  | @cut currentOuter currentHole locals leading trailing child induction =>
      have sourceChildren := sourceCanonical.2
      have leadingAndRest :=
        (ItemSeq.childrenCanonical_append leading
          (.cons (.cut (child.fill before)) trailing)).mp sourceChildren
      have sourceChildCanonical : (child.fill before).Canonical :=
        leadingAndRest.2.1
      have childResult := induction before after sourceChildCanonical
        afterCanonical holeNonempty
      have childCanonical : (child.fill after).Canonical := childResult.1
      constructor
      · constructor
        · intro localIndex
          let localWire := Var.appendRight currentOuter (Var.ofIndex localIndex)
          have childSameNonempty := childResult.2 localWire
          have childSameEmpty :
              (child.fill before).incidencePaths localWire.index.val = [] ↔
                (child.fill after).incidencePaths localWire.index.val = [] := by
            constructor
            · intro sourceEmpty
              by_cases targetEmpty :
                  (child.fill after).incidencePaths localWire.index.val = []
              · exact targetEmpty
              · exact False.elim ((childSameNonempty.mpr targetEmpty) sourceEmpty)
            · intro targetEmpty
              by_cases sourceEmpty :
                  (child.fill before).incidencePaths localWire.index.val = []
              · exact sourceEmpty
              · exact False.elim ((childSameNonempty.mp sourceEmpty) targetEmpty)
          have sourceRoot := sourceCanonical.1 localIndex
          rw [ItemSeq.incidencePaths_frame] at sourceRoot ⊢
          have transformed := (RegionPath.rootedTwo_replace
            (leading.incidencePaths localWire.index.val 0)
            ((child.fill before).incidencePaths localWire.index.val)
            ((child.fill after).incidencePaths localWire.index.val)
            (trailing.incidencePaths localWire.index.val (leading.length + 1))
            leading.length childSameEmpty).mp
              (by simpa [localWire] using sourceRoot)
          simpa [localWire] using transformed
        · apply (ItemSeq.childrenCanonical_append leading
            (.cons (.cut (child.fill after)) trailing)).mpr
          exact ⟨leadingAndRest.1, ⟨childCanonical, leadingAndRest.2.2⟩⟩
      · intro signature wire
        let childWire := wire.appendLeft locals
        have childSameNonempty := childResult.2 childWire
        have childSameEmpty :
            (child.fill before).incidencePaths childWire.index.val = [] ↔
              (child.fill after).incidencePaths childWire.index.val = [] := by
          constructor
          · intro sourceEmpty
            by_cases targetEmpty :
                (child.fill after).incidencePaths childWire.index.val = []
            · exact targetEmpty
            · exact False.elim ((childSameNonempty.mpr targetEmpty) sourceEmpty)
          · intro targetEmpty
            by_cases sourceEmpty :
                (child.fill before).incidencePaths childWire.index.val = []
            · exact sourceEmpty
            · exact False.elim ((childSameNonempty.mp sourceEmpty) targetEmpty)
        simp only [DiagramContext.fill, Region.incidencePaths,
          ItemSeq.incidencePaths_frame]
        simpa [childWire] using RegionPath.nonempty_replace
          (leading.incidencePaths wire.index.val 0)
          ((child.fill before).incidencePaths wire.index.val)
          ((child.fill after).incidencePaths wire.index.val)
          (trailing.incidencePaths wire.index.val (leading.length + 1))
          leading.length (by simpa [childWire] using childSameEmpty)

end DiagramContext

end VisualProof.Diagram
