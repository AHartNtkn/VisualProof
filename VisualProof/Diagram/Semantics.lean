import VisualProof.Diagram.Core

namespace VisualProof

universe u

/-- Every member of a list denotes the same value. -/
def AllEqual (values : List α) : Prop :=
  ∀ left ∈ values, ∀ right ∈ values, left = right

namespace AllEqual

/-- Equality is reflexive for a repeated occurrence. -/
@[simp] theorem refl (value : α) : AllEqual [value] := by
  simp [AllEqual]

/-- Combine two all-equal lists when every cross-pair is equal. -/
theorem append (leftEqual : AllEqual left) (rightEqual : AllEqual right)
    (cross : ∀ leftValue ∈ left, ∀ rightValue ∈ right,
      leftValue = rightValue) :
    AllEqual (left ++ right) := by
  intro first firstMember second secondMember
  simp only [List.mem_append] at firstMember secondMember
  rcases firstMember with firstMember | firstMember <;>
    rcases secondMember with secondMember | secondMember
  · exact leftEqual first firstMember second secondMember
  · exact cross first firstMember second secondMember
  · exact (cross second secondMember first firstMember).symm
  · exact rightEqual first firstMember second secondMember

/-- Two all-equal lists sharing a value form one all-equal union. -/
theorem union (leftEqual : AllEqual left) (rightEqual : AllEqual right)
    (leftContains : pivot ∈ left) (rightContains : pivot ∈ right) :
    AllEqual (left ++ right) :=
  append leftEqual rightEqual fun leftValue leftMember rightValue rightMember =>
    (leftEqual leftValue leftMember pivot leftContains).trans
      (rightEqual pivot rightContains rightValue rightMember)

/-- Storage order cannot affect n-ary identity denotation. -/
theorem perm (permutation : left.Perm right) :
    AllEqual left ↔ AllEqual right := by
  constructor
  · intro equalLeft first firstMember second secondMember
    exact equalLeft first (permutation.mem_iff.mpr firstMember)
      second (permutation.mem_iff.mpr secondMember)
  · intro equalRight first firstMember second secondMember
    exact equalRight first (permutation.mem_iff.mp firstMember)
      second (permutation.mem_iff.mp secondMember)

@[simp] theorem pair (left right : α) :
    AllEqual [left, right] ↔ left = right := by
  constructor
  · intro equal
    exact equal left (by simp) right (by simp)
  · intro equality
    subst right
    simp [AllEqual]

end AllEqual

/-- Typed interpretations of the ordered named-definition context. -/
def DefinitionEnv (pre : PreModel) (defs : List (List Sig)) : Type u :=
  {args : List Sig} →
    DefVar defs args → PreModel.Args pre.Domain args → Prop

namespace DefinitionEnv

/-- Look up a definition at exactly its intrinsic boundary signature. -/
def lookup (definitions : DefinitionEnv pre defs)
    (definition : DefVar defs args) :
    PreModel.Args pre.Domain args → Prop :=
  definitions definition

/-- Pull an interpretation back along a typed definition renaming. -/
def comp (definitions : DefinitionEnv pre target)
    (rho : DefinitionRenaming source target) :
    DefinitionEnv pre source :=
  fun definition => definitions.lookup (rho definition)

end DefinitionEnv

namespace Env

/-- The unique environment for an empty heterogeneous context. -/
def empty : Env pre [] :=
  fun _ var => nomatch var

/-- Pull an environment back along a typed wire renaming. -/
def comp (env : Env pre target) (rho : WireRenaming source target) :
    Env pre source :=
  fun sig var => env sig (rho var)

@[simp] theorem comp_extend (env : Env pre target)
    (rho : WireRenaming source target) (value : pre.Domain bound) :
    comp (env.extend value) (WireRenaming.lift rho bound) =
      (comp env rho).extend value := by
  funext sig var
  cases var <;> rfl

end Env

namespace Vars

@[simp] theorem denote_rename (env : Env pre target)
    (rho : WireRenaming source target) (variables : Vars source args) :
    denote env (variables.rename rho) = denote (Env.comp env rho) variables := by
  induction variables with
  | nil => rfl
  | cons head tail ih =>
      simp only [Vars.rename, denote_cons, Env.comp]
      exact congrArg (fun value => (env _ (rho head), value)) ih

end Vars

mutual
  /-- Denotation of a region delegates to its conjunction of items. -/
  def denoteRegion (pre : PreModel) (definitions : DefinitionEnv pre defs)
      (env : Env pre ctx) : Region defs ctx → Prop
    | .mk items => denoteItemSeq pre definitions env items

  /-- Generic premodel denotation of every intrinsic item constructor. -/
  def denoteItem (pre : PreModel) (definitions : DefinitionEnv pre defs)
      (env : Env pre ctx) : Item defs ctx → Prop
    | .atom head arguments =>
        pre.apply (env _ head) (Vars.denote env arguments)
    | .named definition arguments =>
        definitions.lookup definition (Vars.denote env arguments)
    | .identity sig ports _ =>
        AllEqual (ports.map (env sig))
    | .cut body =>
        ¬ denoteRegion pre definitions env body
    | .bind sig body =>
        ∃ value : pre.Domain sig,
          denoteRegion pre definitions (env.extend value) body

  /-- An intrinsic item sequence denotes conjunction. -/
  def denoteItemSeq (pre : PreModel) (definitions : DefinitionEnv pre defs)
      (env : Env pre ctx) : ItemSeq defs ctx → Prop
    | .nil => True
    | .cons head tail =>
        denoteItem pre definitions env head ∧
          denoteItemSeq pre definitions env tail
end

/-- Truth of a closed diagram in every full higher-order model. -/
def Valid (diagram : Region defs []) : Prop :=
  ∀ (model : Model.{u})
    (definitions : DefinitionEnv model.toPreModel defs),
      denoteRegion model.toPreModel definitions Env.empty diagram

/-- Semantic consequence between closed diagrams in every full model. -/
def Entails (left right : Region defs []) : Prop :=
  ∀ (model : Model.{u})
    (definitions : DefinitionEnv model.toPreModel defs),
      denoteRegion model.toPreModel definitions Env.empty left →
        denoteRegion model.toPreModel definitions Env.empty right

@[simp] theorem denoteRegion_blank
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) :
    denoteRegion pre definitions env (blank : Region defs ctx) := by
  trivial

@[simp] theorem denoteItemSeq_nil
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) :
    denoteItemSeq pre definitions env (.nil : ItemSeq defs ctx) ↔ True :=
  Iff.rfl

@[simp] theorem denoteItemSeq_cons
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (head : Item defs ctx) (tail : ItemSeq defs ctx) :
    denoteItemSeq pre definitions env (.cons head tail) ↔
      denoteItem pre definitions env head ∧
        denoteItemSeq pre definitions env tail :=
  Iff.rfl

@[simp] theorem denoteItemSeq_append
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (left right : ItemSeq defs ctx) :
    denoteItemSeq pre definitions env (left.append right) ↔
      denoteItemSeq pre definitions env left ∧
        denoteItemSeq pre definitions env right := by
  cases left with
  | nil => simp
  | cons head tail =>
      rw [ItemSeq.append, denoteItemSeq_cons,
        denoteItemSeq_append pre definitions env tail right]
      constructor
      · rintro ⟨headDenotes, tailDenotes, rightDenotes⟩
        exact ⟨⟨headDenotes, tailDenotes⟩, rightDenotes⟩
      · rintro ⟨⟨headDenotes, tailDenotes⟩, rightDenotes⟩
        exact ⟨headDenotes, tailDenotes, rightDenotes⟩

namespace Region

@[simp] theorem denote_conjoin
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (left right : Region defs ctx) :
    denoteRegion pre definitions env (left.conjoin right) ↔
      denoteRegion pre definitions env left ∧
        denoteRegion pre definitions env right := by
  cases left
  cases right
  exact denoteItemSeq_append pre definitions env _ _

end Region

@[simp] theorem denoteItem_atom
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (head : Var ctx (.rel args))
    (arguments : Vars ctx args) :
    denoteItem pre definitions env (.atom head arguments) ↔
      pre.apply (env _ head) (Vars.denote env arguments) :=
  Iff.rfl

@[simp] theorem denoteItem_named
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (definition : DefVar defs args)
    (arguments : Vars ctx args) :
    denoteItem pre definitions env (.named definition arguments) ↔
      definitions.lookup definition (Vars.denote env arguments) :=
  Iff.rfl

@[simp] theorem denoteItem_identity
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (ports : List (Var ctx sig))
    (atLeastTwo : 2 ≤ ports.length) :
    denoteItem pre definitions env (.identity sig ports atLeastTwo) ↔
      AllEqual (ports.map (env sig)) :=
  Iff.rfl

@[simp] theorem binary_identity
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (left right : Var ctx sig) :
    denoteItem pre definitions env
        (Item.binaryIdentity sig left right) ↔
      env sig left = env sig right := by
  simp only [Item.binaryIdentity, denoteItem_identity, List.map_cons,
    List.map_nil, AllEqual.pair]

@[simp] theorem cut_denotes_negation
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (body : Region defs ctx) :
    denoteItem pre definitions env (.cut body) ↔
      ¬ denoteRegion pre definitions env body :=
  Iff.rfl

@[simp] theorem bind_denotes_exists
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (body : Region defs (sig :: ctx)) :
    denoteItem pre definitions env (.bind sig body) ↔
      ∃ value : pre.Domain sig,
        denoteRegion pre definitions (env.extend value) body :=
  Iff.rfl

/-- Wire renaming preserves region denotation under environment pullback. -/
theorem denoteRegion_renameWires
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre target) (rho : WireRenaming source target)
    (region : Region defs source) :
    denoteRegion pre definitions env (region.renameWires rho) ↔
      denoteRegion pre definitions (Env.comp env rho) region := by
  refine Region.rec
    (motive_1 := fun source region =>
      ∀ {target} (env : Env pre target)
        (rho : WireRenaming source target),
        denoteRegion pre definitions env (region.renameWires rho) ↔
          denoteRegion pre definitions (Env.comp env rho) region)
    (motive_2 := fun source item =>
      ∀ {target} (env : Env pre target)
        (rho : WireRenaming source target),
        denoteItem pre definitions env (item.renameWires rho) ↔
          denoteItem pre definitions (Env.comp env rho) item)
    (motive_3 := fun source items =>
      ∀ {target} (env : Env pre target)
        (rho : WireRenaming source target),
        denoteItemSeq pre definitions env (items.renameWires rho) ↔
          denoteItemSeq pre definitions (Env.comp env rho) items)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ region env rho
  · intro _ items itemsLaw _ env rho
    exact itemsLaw env rho
  · intro _ _ head arguments _ env rho
    simp [Item.renameWires, Env.comp]
  · intro _ _ definition arguments _ env rho
    simp [Item.renameWires]
  · intro _ sig ports atLeastTwo _ env rho
    simp only [Item.renameWires, denoteItem_identity, List.map_map]
    rfl
  · intro _ body bodyLaw _ env rho
    simp only [Item.renameWires, cut_denotes_negation, bodyLaw]
  · intro _ sig body bodyLaw _ env rho
    simp only [Item.renameWires, bind_denotes_exists, bodyLaw,
      Env.comp_extend]
  · intro _ _ env rho
    rfl
  · intro _ head tail headLaw tailLaw _ env rho
    simp only [ItemSeq.renameWires, denoteItemSeq_cons, headLaw, tailLaw]

/-- Wire renaming preserves item denotation under environment pullback. -/
theorem denoteItem_renameWires
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre target) (rho : WireRenaming source target)
    (item : Item defs source) :
    denoteItem pre definitions env (item.renameWires rho) ↔
      denoteItem pre definitions (Env.comp env rho) item := by
  have regionLaw := denoteRegion_renameWires pre definitions env rho
    (Region.mk (.cons item .nil))
  simpa [denoteRegion, Region.renameWires, ItemSeq.renameWires,
    denoteItemSeq] using regionLaw

/-- Wire renaming preserves conjunction denotation under pullback. -/
theorem denoteItemSeq_renameWires
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre target) (rho : WireRenaming source target)
    (items : ItemSeq defs source) :
    denoteItemSeq pre definitions env (items.renameWires rho) ↔
      denoteItemSeq pre definitions (Env.comp env rho) items := by
  exact denoteRegion_renameWires pre definitions env rho (.mk items)

/-- Definition renaming preserves region denotation under interpretation pullback. -/
theorem denoteRegion_renameDefinitions
    (pre : PreModel) (definitions : DefinitionEnv pre target)
    (rho : DefinitionRenaming source target) (env : Env pre ctx)
    (region : Region source ctx) :
    denoteRegion pre definitions env (region.renameDefinitions rho) ↔
      denoteRegion pre (definitions.comp rho) env region := by
  refine Region.rec
    (motive_1 := fun ctx region => ∀ env : Env pre ctx,
      denoteRegion pre definitions env (region.renameDefinitions rho) ↔
        denoteRegion pre (definitions.comp rho) env region)
    (motive_2 := fun ctx item => ∀ env : Env pre ctx,
      denoteItem pre definitions env (item.renameDefinitions rho) ↔
        denoteItem pre (definitions.comp rho) env item)
    (motive_3 := fun ctx items => ∀ env : Env pre ctx,
      denoteItemSeq pre definitions env (items.renameDefinitions rho) ↔
        denoteItemSeq pre (definitions.comp rho) env items)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ region env
  · intro _ items itemsLaw env
    exact itemsLaw env
  · intro _ _ head arguments env
    rfl
  · intro _ _ definition arguments env
    rfl
  · intro _ sig ports atLeastTwo env
    rfl
  · intro _ body bodyLaw env
    simp only [Item.renameDefinitions, cut_denotes_negation, bodyLaw]
  · intro _ sig body bodyLaw env
    simp only [Item.renameDefinitions, bind_denotes_exists, bodyLaw]
  · intro _ env
    rfl
  · intro _ head tail headLaw tailLaw env
    simp only [ItemSeq.renameDefinitions, denoteItemSeq_cons,
      headLaw, tailLaw]

/-- Definition renaming preserves item denotation under interpretation pullback. -/
theorem denoteItem_renameDefinitions
    (pre : PreModel) (definitions : DefinitionEnv pre target)
    (rho : DefinitionRenaming source target) (env : Env pre ctx)
    (item : Item source ctx) :
    denoteItem pre definitions env (item.renameDefinitions rho) ↔
      denoteItem pre (definitions.comp rho) env item := by
  have regionLaw := denoteRegion_renameDefinitions pre definitions rho env
    (Region.mk (.cons item .nil))
  simpa [denoteRegion, Region.renameDefinitions, ItemSeq.renameDefinitions,
    denoteItemSeq] using regionLaw

/-- Definition renaming preserves conjunction denotation under pullback. -/
theorem denoteItemSeq_renameDefinitions
    (pre : PreModel) (definitions : DefinitionEnv pre target)
    (rho : DefinitionRenaming source target) (env : Env pre ctx)
    (items : ItemSeq source ctx) :
    denoteItemSeq pre definitions env (items.renameDefinitions rho) ↔
      denoteItemSeq pre (definitions.comp rho) env items := by
  exact denoteRegion_renameDefinitions pre definitions rho env (.mk items)

/-- Capture-avoiding typed substitution obeys the wire-renaming semantic law. -/
theorem denoteRegion_substitute
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre target) (substitution : WireSubstitution source target)
    (region : Region defs source) :
    denoteRegion pre definitions env (region.substitute substitution) ↔
      denoteRegion pre definitions (Env.comp env substitution) region :=
  denoteRegion_renameWires pre definitions env substitution region

/-- Capture-avoiding typed substitution preserves item denotation. -/
theorem denoteItem_substitute
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre target) (substitution : WireSubstitution source target)
    (item : Item defs source) :
    denoteItem pre definitions env (item.substitute substitution) ↔
      denoteItem pre definitions (Env.comp env substitution) item :=
  denoteItem_renameWires pre definitions env substitution item

/-- Capture-avoiding typed substitution preserves sequence denotation. -/
theorem denoteItemSeq_substitute
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre target) (substitution : WireSubstitution source target)
    (items : ItemSeq defs source) :
    denoteItemSeq pre definitions env (items.substitute substitution) ↔
      denoteItemSeq pre definitions (Env.comp env substitution) items :=
  denoteItemSeq_renameWires pre definitions env substitution items

/-! Executable semantic acceptance examples. -/

example : Valid (blank : Region defs []) := by
  simp [Valid]

example (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (x y : Var ctx sig) :
    denoteItem pre definitions env (Item.binaryIdentity sig x y) ↔
      env sig x = env sig y := by
  simp

example (pre : PreModel) (env : Env pre ctx)
    (ports₁ ports₂ : List (Var ctx sig))
    (permutation : ports₁.Perm ports₂) :
    AllEqual (ports₁.map (env sig)) ↔ AllEqual (ports₂.map (env sig)) := by
  exact AllEqual.perm (permutation.map (env sig))

example (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (body : Region defs (sig :: ctx)) :
    denoteItem pre definitions env (.bind sig body) ↔
      ∃ value : pre.Domain sig,
        denoteRegion pre definitions (env.extend value) body := by
  rfl

example (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre target) (substitution : WireSubstitution source target)
    (region : Region defs source) :
    denoteRegion pre definitions env (region.substitute substitution) ↔
      denoteRegion pre definitions (Env.comp env substitution) region :=
  denoteRegion_substitute pre definitions env substitution region

end VisualProof
