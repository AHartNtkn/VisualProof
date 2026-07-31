import VisualProof.Rule.WirePrimitive.Witness

namespace VisualProof

namespace WirePrimitive

namespace ContentWitnesses

universe u

/-- One full-model relation value at a fixed ordered signature. -/
abbrev RelationValue
    (model : Model.{u}) (arguments : List Sig) :=
  Sig.denote model.Carrier (.rel arguments)

/-- Pointwise complement exists because a full model contains every relation. -/
def complement
    (relation : RelationValue model arguments) :
    RelationValue model arguments :=
  fun values => ¬ relation values

/-- Pointwise intersection exists because a full model contains every relation. -/
def intersect
    (left right : RelationValue model arguments) :
    RelationValue model arguments :=
  fun values => left values ∧ right values

/-- The logical all-site rewrite induced by wrapping each application in a cut. -/
def cutRewrite
    (model : Model.{u})
    (siteContext : UniformSiteContext siteCount)
    (argumentsAt :
      Fin siteCount →
        PreModel.Args model.toPreModel.Domain arguments) :
    LogicalUniformRewrite siteCount
      (RelationValue model arguments)
      (RelationValue model arguments) :=
  LogicalUniformRewrite.ofContext siteContext
    (fun relation site =>
      model.toPreModel.apply relation (argumentsAt site))
    (fun relation site =>
      ¬model.toPreModel.apply relation (argumentsAt site))

/-- Complementing the target relation eliminates the source cut-wrap binder. -/
def cutEliminating
    (model : Model.{u})
    (siteContext : UniformSiteContext siteCount)
    (argumentsAt :
      Fin siteCount →
        PreModel.Args model.toPreModel.Domain arguments) :
    HasEliminatingWitness
      (cutRewrite model siteContext argumentsAt) where
  witness := complement
  pointwise := by
    intro target site
    exact Iff.rfl

/-- Complementing the source relation introduces the target cut-wrap binder. -/
noncomputable def cutIntroducing
    (model : Model.{u})
    (siteContext : UniformSiteContext siteCount)
    (argumentsAt :
      Fin siteCount →
        PreModel.Args model.toPreModel.Domain arguments) :
    HasIntroducingWitness
      (cutRewrite model siteContext argumentsAt) where
  witness := complement
  pointwise := by
    intro source site
    change
      model.toPreModel.apply source (argumentsAt site) ↔
        ¬¬model.toPreModel.apply source (argumentsAt site)
    exact Classical.not_not.symm

/-- The cut-wrap site bodies are equivalent for one shared complement witness. -/
theorem cutBodyEquivalence
    (model : Model.{u})
    (siteContext : UniformSiteContext siteCount)
    (argumentsAt :
      Fin siteCount →
        PreModel.Args model.toPreModel.Domain arguments) :
    (cutRewrite model siteContext argumentsAt).sourceInner ↔
      (cutRewrite model siteContext argumentsAt).targetInner :=
  uniform_body_equivalence (cutRewrite model siteContext argumentsAt)
    (cutEliminating model siteContext argumentsAt)
    (cutIntroducing model siteContext argumentsAt)

/--
The logical all-site rewrite induced by replacing one relation application
with two co-located applications.
-/
def parallelRewrite
    (model : Model.{u})
    (siteContext : UniformSiteContext siteCount)
    (argumentsAt :
      Fin siteCount →
        PreModel.Args model.toPreModel.Domain arguments) :
    LogicalUniformRewrite siteCount
      (RelationValue model arguments)
      (RelationValue model arguments × RelationValue model arguments) :=
  LogicalUniformRewrite.ofContext siteContext
    (fun relation site =>
      model.toPreModel.apply relation (argumentsAt site))
    (fun relations site =>
      model.toPreModel.apply relations.1 (argumentsAt site) ∧
        model.toPreModel.apply relations.2 (argumentsAt site))

/-- Intersecting the two target relations eliminates the source split binder. -/
def parallelEliminating
    (model : Model.{u})
    (siteContext : UniformSiteContext siteCount)
    (argumentsAt :
      Fin siteCount →
        PreModel.Args model.toPreModel.Domain arguments) :
    HasEliminatingWitness
      (parallelRewrite model siteContext argumentsAt) where
  witness := fun relations => intersect relations.1 relations.2
  pointwise := by
    intro target site
    exact Iff.rfl

/-- Diagonal copying introduces both target relations from one source value. -/
def parallelIntroducing
    (model : Model.{u})
    (siteContext : UniformSiteContext siteCount)
    (argumentsAt :
      Fin siteCount →
        PreModel.Args model.toPreModel.Domain arguments) :
    HasIntroducingWitness
      (parallelRewrite model siteContext argumentsAt) where
  witness := fun source => (source, source)
  pointwise := by
    intro source site
    constructor
    · intro holds
      exact ⟨holds, holds⟩
    · exact And.left

/--
The parallel-split site bodies are equivalent for one shared intersection
witness and the reverse diagonal witness.
-/
theorem parallelBodyEquivalence
    (model : Model.{u})
    (siteContext : UniformSiteContext siteCount)
    (argumentsAt :
      Fin siteCount →
        PreModel.Args model.toPreModel.Domain arguments) :
    (parallelRewrite model siteContext argumentsAt).sourceInner ↔
      (parallelRewrite model siteContext argumentsAt).targetInner :=
  uniform_body_equivalence (parallelRewrite model siteContext argumentsAt)
    (parallelEliminating model siteContext argumentsAt)
    (parallelIntroducing model siteContext argumentsAt)

end ContentWitnesses

end WirePrimitive

end VisualProof
