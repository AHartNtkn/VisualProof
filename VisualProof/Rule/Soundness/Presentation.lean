import VisualProof.Diagram.Semantics.Context
import VisualProof.Rule.Presentation
import VisualProof.Rule.Soundness.Contextual

namespace VisualProof.Rule

open Theory
open Diagram

namespace Presentation

namespace Configuration

def Denotes (model : Model) (env : Values model wires) :
    Configuration wires signature → Prop
  | [] => True
  | node :: tail =>
      denoteItem model env node.item ∧ Configuration.Denotes model env tail

theorem Denotes.node
    {wires : List Sig} {signature : Sig}
    {model : Model} {env : Values model wires}
    {configuration : Configuration wires signature}
    {node : Node wires signature}
    (denotes : configuration.Denotes model env)
    (member : node ∈ configuration) :
    denoteItem model env node.item := by
  induction configuration with
  | nil => simp at member
  | cons head tail induction =>
      rcases denotes with ⟨headDenotes, tailDenotes⟩
      rcases List.mem_cons.mp member with equality | tailMember
      · subst node
        exact headDenotes
      · exact induction tailDenotes tailMember

theorem Generated.mono
    {source target : Configuration wires signature}
    (adjacent : ∀ {left right}, source.Adjacent left right →
      target.Adjacent left right)
    {left right : Var wires signature}
    (generated : source.Generated left right) :
    target.Generated left right := by
  induction generated with
  | refl wire => exact .refl wire
  | adjacent evidence => exact .adjacent (adjacent evidence)
  | symm evidence induction => exact .symm induction
  | trans first second firstIH secondIH => exact .trans firstIH secondIH

theorem Denotes.generated_eq
    {wires : List Sig} {signature : Sig}
    {model : Model} {env : Values model wires}
    {configuration : Configuration wires signature}
    {left right : Var wires signature}
    (denotes : configuration.Denotes model env)
    (generated : configuration.Generated left right) :
    env.lookup left = env.lookup right := by
  induction generated with
  | refl wire => rfl
  | adjacent evidence =>
      rcases evidence with ⟨node, nodeMember, leftMember, rightMember⟩
      have nodeDenotes := denotes.node nodeMember
      obtain ⟨leftIndex, leftEq⟩ := (List.mem_ofFn).mp leftMember
      obtain ⟨rightIndex, rightEq⟩ := (List.mem_ofFn).mp rightMember
      have equality := nodeDenotes leftIndex rightIndex
      rw [leftEq, rightEq] at equality
      exact equality
  | symm evidence induction => exact induction.symm
  | trans first second firstIH secondIH => exact firstIH.trans secondIH

theorem denotes_of_generated_eq
    {wires : List Sig} {signature : Sig}
    {model : Model} {env : Values model wires}
    {configuration : Configuration wires signature}
    (generatedEq : ∀ left right,
      configuration.Generated left right →
        env.lookup left = env.lookup right) :
    configuration.Denotes model env := by
  induction configuration with
  | nil => trivial
  | cons node tail induction =>
      constructor
      · intro left right
        apply generatedEq (node.ports left) (node.ports right)
        exact .adjacent ⟨node, by simp, (List.mem_ofFn).mpr ⟨left, rfl⟩,
          (List.mem_ofFn).mpr ⟨right, rfl⟩⟩
      · apply induction
        intro left right tailGenerated
        apply generatedEq left right
        exact tailGenerated.mono (by
          rintro adjacentLeft adjacentRight
            ⟨memberNode, member, leftMember, rightMember⟩
          exact ⟨memberNode, List.mem_cons_of_mem node member,
            leftMember, rightMember⟩)

theorem denotes_iff_of_sameRelation
    {wires : List Sig} {signature : Sig}
    {model : Model} {env : Values model wires}
    {source target : Configuration wires signature}
    (sameRelation : source.SameRelation target) :
    source.Denotes model env ↔ target.Denotes model env := by
  constructor
  · intro sourceDenotes
    apply denotes_of_generated_eq
    intro left right targetGenerated
    exact sourceDenotes.generated_eq
      ((sameRelation left right).mpr targetGenerated)
  · intro targetDenotes
    apply denotes_of_generated_eq
    intro left right sourceGenerated
    exact targetDenotes.generated_eq
      ((sameRelation left right).mp sourceGenerated)

theorem denoteItems_iff
    (configuration : Configuration wires signature) :
    denoteItemSeq model env configuration.items ↔
      configuration.Denotes model env := by
  induction configuration with
  | nil => rfl
  | cons node tail induction =>
      simp only [items, denoteItemSeq_cons, Denotes]
      rw [induction]

end Configuration

theorem denote_region_iff
    (locals : List Sig) (retained : ItemSeq (outer ++ locals))
    (source target : Configuration (outer ++ locals) signature)
    (sameRelation : source.SameRelation target)
    (model : Model) (env : Values model outer) :
    denoteRegion model env (region locals retained source) ↔
      denoteRegion model env (region locals retained target) := by
  simp only [region, denoteRegion_mk]
  constructor
  · rintro ⟨localEnv, sourceDenotes⟩
    refine ⟨localEnv, ?_⟩
    rw [denoteItemSeq_append] at sourceDenotes ⊢
    refine ⟨sourceDenotes.1, ?_⟩
    apply (Configuration.denoteItems_iff target).mpr
    apply (Configuration.denotes_iff_of_sameRelation sameRelation).mp
    exact (Configuration.denoteItems_iff source).mp sourceDenotes.2
  · rintro ⟨localEnv, targetDenotes⟩
    refine ⟨localEnv, ?_⟩
    rw [denoteItemSeq_append] at targetDenotes ⊢
    refine ⟨targetDenotes.1, ?_⟩
    apply (Configuration.denoteItems_iff source).mpr
    apply (Configuration.denotes_iff_of_sameRelation sameRelation).mpr
    exact (Configuration.denoteItems_iff target).mp targetDenotes.2

theorem Local.sound_iff
    {before after : Region wires} (step : Local before after)
    (model : Model) (env : Values model wires) :
    denoteRegion model env before ↔ denoteRegion model env after := by
  cases step with
  | replace locals retained signature source target applicability =>
      exact denote_region_iff locals retained source target
        applicability.sameRelation model env

end Presentation

theorem Presentation.sound
    {source target : OpenDiagram boundary}
    (step : Presentation source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args → denoteOpen model target args := by
  apply Contextual.sound (step := step)
  intro wires before after localStep model env
  rcases localStep with forward | backward
  · exact (Presentation.Local.sound_iff forward model env).mp
  · exact (Presentation.Local.sound_iff backward model env).mpr

theorem Presentation.sound_iff
    {source target : OpenDiagram boundary}
    (step : Presentation source target)
    (model : Model) (args : Values model boundary) :
    denoteOpen model source args ↔ denoteOpen model target args := by
  constructor
  · exact Presentation.sound step model args
  · exact Presentation.sound (Presentation.symm step) model args

end VisualProof.Rule
