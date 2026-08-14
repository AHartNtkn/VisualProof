import VisualProof.Diagram.Environment

namespace VisualProof.Diagram

open VisualProof
open Theory

mutual
  def denoteRegion (model : Model) (env : Values model outer) :
      Region outer → Prop
    | .mk locals items =>
        ∃ localEnv : Values model locals,
          denoteItemSeq model (env.append localEnv) items

  def denoteItem (model : Model) (env : Values model wires) :
      Item wires → Prop
    | .atom head ports =>
        env.lookup head (evaluateVars ports env)
    | .identity _ arity ports =>
        ∀ left right : Fin arity,
          env.lookup (ports left) = env.lookup (ports right)
    | .cut body => Not (denoteRegion model env body)

  def denoteItemSeq (model : Model) (env : Values model wires) :
      ItemSeq wires → Prop
    | .nil => True
    | .cons head tail =>
        denoteItem model env head ∧ denoteItemSeq model env tail
end

def denoteOpen (model : Model) (diagram : OpenDiagram boundary)
    (args : Values model boundary) : Prop :=
  ∃ externalEnv : Values model diagram.external,
    evaluateVars diagram.boundaryWire externalEnv = args ∧
      denoteRegion model externalEnv diagram.body

@[simp] theorem denoteRegion_mk
    (model : Model) (env : Values model outer)
    (locals : List Sig) (items : ItemSeq (outer ++ locals)) :
    denoteRegion model env (.mk locals items) ↔
      ∃ localEnv : Values model locals,
        denoteItemSeq model (env.append localEnv) items := by
  rfl

@[simp] theorem denoteItem_atom
    (model : Model) (env : Values model wires)
    (head : Var wires (.rel arguments)) (ports : Vars wires arguments) :
    denoteItem model env (.atom head ports) ↔
      env.lookup head (evaluateVars ports env) := by
  rfl

@[simp] theorem denoteItem_identity
    (model : Model) (env : Values model wires)
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) :
    denoteItem model env (.identity signature arity ports) ↔
      ∀ left right : Fin arity,
        env.lookup (ports left) = env.lookup (ports right) := by
  rfl

@[simp] theorem denoteItem_cut
    (model : Model) (env : Values model wires) (body : Region wires) :
    denoteItem model env (.cut body) ↔ Not (denoteRegion model env body) := by
  rfl

@[simp] theorem denoteItemSeq_nil
    (model : Model) (env : Values model wires) :
    denoteItemSeq model env (.nil : ItemSeq wires) ↔ True := by
  rfl

@[simp] theorem denoteItemSeq_cons
    (model : Model) (env : Values model wires)
    (head : Item wires) (tail : ItemSeq wires) :
    denoteItemSeq model env (.cons head tail) ↔
      denoteItem model env head ∧ denoteItemSeq model env tail := by
  rfl

theorem denoteItem_unary_identity
    (model : Model) (env : Values model wires)
    (wire : Var wires signature) :
    denoteItem model env (.identity signature 1 (fun _ => wire)) := by
  intro left right
  have : left = right := Subsingleton.elim _ _
  rw [this]

theorem OpenDiagram.denote_body
    {diagram : OpenDiagram boundary}
    {before after : Region diagram.external}
    {beforeCanonical : before.Canonical}
    {afterCanonical : after.Canonical}
    {beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      diagram.boundaryWire before}
    {afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      diagram.boundaryWire after}
    {model : Model} {args : Values model boundary}
    (implication : ∀ env : Values model diagram.external,
      denoteRegion model env before → denoteRegion model env after) :
    denoteOpen model (diagram.withBody before beforeCanonical
      beforeExternalTwoEnded) args →
      denoteOpen model (diagram.withBody after afterCanonical
        afterExternalTwoEnded) args := by
  rintro ⟨externalEnv, boundaryEq, beforeDenotes⟩
  exact ⟨externalEnv, boundaryEq, implication externalEnv beforeDenotes⟩

theorem OpenDiagram.denote_body_iff
    {diagram : OpenDiagram boundary}
    {before after : Region diagram.external}
    {beforeCanonical : before.Canonical}
    {afterCanonical : after.Canonical}
    {beforeExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      diagram.boundaryWire before}
    {afterExternalTwoEnded : OpenDiagram.ExternalTwoEnded
      diagram.boundaryWire after}
    {model : Model} {args : Values model boundary}
    (equivalence : ∀ env : Values model diagram.external,
      denoteRegion model env before ↔ denoteRegion model env after) :
    denoteOpen model (diagram.withBody before beforeCanonical
      beforeExternalTwoEnded) args ↔
      denoteOpen model (diagram.withBody after afterCanonical
        afterExternalTwoEnded) args := by
  constructor
  · exact OpenDiagram.denote_body fun env => (equivalence env).mp
  · exact OpenDiagram.denote_body fun env => (equivalence env).mpr

end VisualProof.Diagram
