import VisualProof.Diagram.Context
import VisualProof.Diagram.Scope

namespace VisualProof.Diagram

open VisualProof.Theory

namespace DiagramContext

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
