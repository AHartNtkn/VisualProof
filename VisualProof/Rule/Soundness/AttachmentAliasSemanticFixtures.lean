import VisualProof.Rule.Soundness.AttachmentAliasSemantic

namespace VisualProof.Rule.AttachmentAliasSemanticFixtures

open VisualProof
open VisualProof.Diagram
open VisualProof.Diagram.Splice
open VisualProof.Diagram.Splice.AttachmentAliasMaterialization

private def twoRootWires : ConcreteDiagram where
  regionCount := 1
  nodeCount := 0
  wireCount := 2
  root := 0
  regions := fun _ => .sheet
  nodes := nofun
  wires := fun _ => { scope := 0, endpoints := [] }

private def distinctBoundary : OpenConcreteDiagram where
  diagram := twoRootWires
  boundary := [⟨0, by decide⟩, ⟨1, by decide⟩]

private def sharedHost : Fin distinctBoundary.boundary.length → Nat := fun _ => 0

private def oneRootWire : ConcreteDiagram where
  regionCount := 1
  nodeCount := 0
  wireCount := 1
  root := 0
  regions := fun _ => .sheet
  nodes := nofun
  wires := fun _ => { scope := 0, endpoints := [] }

private def repeatedBoundary : OpenConcreteDiagram where
  diagram := oneRootWire
  boundary := [⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]

private def distinctThenReuse : Fin repeatedBoundary.boundary.length → Nat :=
  fun position => if position.val = 0 then 0 else 1

/-- Distinct intrinsic identities sharing one host attachment do not create an
alias identity and remain distinct after executable materialization. -/
example : aliasCount distinctBoundary sharedHost = 0 := by decide

example : rawBoundaryWire distinctBoundary sharedHost ⟨0, by decide⟩ ≠
    rawBoundaryWire distinctBoundary sharedHost ⟨1, by decide⟩ := by decide

/-- One distinct extra attachment materializes exactly one identity. -/
example : aliasCount repeatedBoundary distinctThenReuse = 1 := by decide

example : rawBoundaryWire repeatedBoundary distinctThenReuse ⟨0, by decide⟩ ≠
    rawBoundaryWire repeatedBoundary distinctThenReuse ⟨1, by decide⟩ := by
  decide

/-- Repeating the same intrinsic/host pair reuses the materialized identity. -/
example : rawBoundaryWire repeatedBoundary distinctThenReuse ⟨1, by decide⟩ =
    rawBoundaryWire repeatedBoundary distinctThenReuse ⟨2, by decide⟩ := by
  decide

/-- Zero-alias semantic specialization. -/
example {signature : List Nat} {Host : Type} [DecidableEq Host]
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {spine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment spine)
    (halias : aliasCount pattern.val attachment = 0)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (args : Fin pattern.val.boundary.length → model.Carrier) :
    aliasCount pattern.val attachment = 0 ∧
      (certificate.result.denote model named
          (args ∘ Fin.cast certificate.boundary_length) ↔
        pattern.denote model named args) := by
  exact ⟨halias, certificate.denote_iff model named args⟩

/-- One-extra-attachment and exact-pair-reuse specializations share the same
model-independent theorem surface. -/
example {signature : List Nat} {Host : Type} [DecidableEq Host]
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {spine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment spine)
    (hone : aliasCount pattern.val attachment = 1)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (args : Fin pattern.val.boundary.length → model.Carrier) :
    aliasCount pattern.val attachment = 1 ∧
      (certificate.result.denote model named
          (args ∘ Fin.cast certificate.boundary_length) ↔
        pattern.denote model named args) := by
  exact ⟨hone, certificate.denote_iff model named args⟩

/-- Nonempty binder spines use the same general semantic theorem; no root-only
specialization is involved. -/
example {signature : List Nat} {Host : Type} [DecidableEq Host]
    {pattern : CheckedOpenDiagram signature}
    {attachment : Fin pattern.val.boundary.length → Host}
    {spine : BinderSpine pattern.val.diagram}
    (certificate : Certificate pattern attachment spine)
    (hnonempty : spine.proxyCount ≠ 0)
    (model : Lambda.LambdaModel) (named : NamedEnv model.Carrier signature)
    (args : Fin pattern.val.boundary.length → model.Carrier) :
    spine.proxyCount ≠ 0 ∧
      (certificate.result.denote model named
          (args ∘ Fin.cast certificate.boundary_length) ↔
        pattern.denote model named args) := by
  exact ⟨hnonempty, certificate.denote_iff model named args⟩

end VisualProof.Rule.AttachmentAliasSemanticFixtures
