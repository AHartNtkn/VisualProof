import VisualProof.Theory.Definition

namespace VisualProof

namespace DefinitionEnv

/-- The unique interpretation of an empty definition context. -/
def empty : DefinitionEnv pre [] :=
  fun {_} reference => nomatch reference

/-- Extend a typed interpretation by one chronologically newest definition. -/
def cons (latest : PreModel.Args pre.Domain latestArgs → Prop)
    (priorEnv : DefinitionEnv pre prior) :
    DefinitionEnv pre (latestArgs :: prior) :=
  fun {_} reference =>
    match reference with
    | .here => latest
    | .there earlier => DefinitionEnv.lookup priorEnv earlier

/-- The newest relation interpretation. -/
def head (env : DefinitionEnv pre (latestArgs :: prior)) :
    PreModel.Args pre.Domain latestArgs → Prop :=
  DefinitionEnv.lookup env .here

/-- Forget the newest interpretation and expose the prior prefix. -/
def tail (env : DefinitionEnv pre (latestArgs :: prior)) :
    DefinitionEnv pre prior :=
  fun earlier => DefinitionEnv.lookup env (.there earlier)

@[simp] theorem lookup_cons_here
    (latest : PreModel.Args pre.Domain latestArgs → Prop)
    (priorEnv : DefinitionEnv pre prior) :
    DefinitionEnv.lookup (cons latest priorEnv)
        (.here : DefVar (latestArgs :: prior) latestArgs) =
      latest :=
  rfl

@[simp] theorem lookup_cons_there
    (latest : PreModel.Args pre.Domain latestArgs → Prop)
    (priorEnv : DefinitionEnv pre prior)
    (reference : DefVar prior args) :
    DefinitionEnv.lookup (cons latest priorEnv) (.there reference) =
      DefinitionEnv.lookup priorEnv reference :=
  rfl

@[simp] theorem head_cons
    (latest : PreModel.Args pre.Domain latestArgs → Prop)
    (priorEnv : DefinitionEnv pre prior) :
    head (cons latest priorEnv) = latest :=
  rfl

@[simp] theorem lookup_tail_cons
    (latest : PreModel.Args pre.Domain latestArgs → Prop)
    (priorEnv : DefinitionEnv pre prior)
    (reference : DefVar prior args) :
    DefinitionEnv.lookup (tail (cons latest priorEnv)) reference =
      DefinitionEnv.lookup priorEnv reference :=
  rfl

end DefinitionEnv

namespace DefinitionData

/--
Interpret an ordered definition store in a full model. Each newest predicate is
derived from its stored open body over the already-interpreted prior prefix.
-/
def denote (model : Model) :
    {signatures : List (List Sig)} →
      DefinitionData signatures →
      DefinitionEnv model.toPreModel signatures
  | [], .nil => DefinitionEnv.empty
  | _ :: _, .snoc priorData _ definition =>
      let priorEnv : DefinitionEnv model.toPreModel _ :=
        fun reference => denote model priorData reference
      DefinitionEnv.cons
        (fun values =>
          denoteOpen model.toPreModel priorEnv definition.body values)
        priorEnv

/--
The stored-body meaning of one typed definition under an arbitrary generic
interpretation. Traversal drops later definitions before denoting an earlier
body, preserving the exact chronological dependency prefix.
-/
def bodyMeaning (pre : PreModel) :
    {signatures : List (List Sig)} →
      (data : DefinitionData signatures) →
      DefinitionEnv pre signatures →
      {args : List Sig} →
      DefVar signatures args →
      PreModel.Args pre.Domain args → Prop
  | [], .nil, _, _, reference, _ => nomatch reference
  | _ :: _, .snoc _ _ definition, env, _, .here, values =>
      denoteOpen pre (DefinitionEnv.tail env) definition.body values
  | _ :: _, .snoc priorData _ _, env, _, .there earlier, values =>
      bodyMeaning pre priorData (DefinitionEnv.tail env) earlier values

/--
A generic interpretation is lawful precisely when every entry agrees with its
stored body over the lawful prior prefix.
-/
def Lawful (pre : PreModel) :
    {signatures : List (List Sig)} →
      DefinitionData signatures →
      DefinitionEnv pre signatures → Prop
  | [], .nil, _ => True
  | _ :: _, .snoc priorData _ definition, env =>
      Lawful pre priorData (DefinitionEnv.tail env) ∧
        ∀ values,
          DefinitionEnv.head env values ↔
            denoteOpen pre (DefinitionEnv.tail env) definition.body values

/-- Lawfulness exposes exact stored-body meaning for every typed reference. -/
theorem lookup_iff_body
    (data : DefinitionData signatures)
    (env : DefinitionEnv pre signatures)
    (lawful : data.Lawful pre env)
    (reference : DefVar signatures args)
    (values : PreModel.Args pre.Domain args) :
    DefinitionEnv.lookup env reference values ↔
      data.bodyMeaning pre env reference values := by
  induction data with
  | nil =>
      exact nomatch reference
  | snoc priorData latestArgs definition induction =>
      cases reference with
      | here =>
          exact lawful.2 values
      | there earlier =>
          exact induction (DefinitionEnv.tail env) lawful.1 earlier

/-- The recursively derived full-model interpretation is lawful. -/
theorem denote_lawful
    (data : DefinitionData signatures) (model : Model) :
    data.Lawful model.toPreModel (data.denote model) := by
  induction data with
  | nil =>
      trivial
  | snoc priorData latestArgs definition induction =>
      constructor
      · simpa [denote] using induction
      · intro values
        rfl

end DefinitionData

/-- Generic lawfulness for one hidden-index ordered definition store. -/
def DefinitionLawful (pre : PreModel) (definitions : Definitions)
    (env : DefinitionEnv pre definitions.signatures) : Prop :=
  definitions.data.Lawful pre env

namespace Definitions

/-- Recursively interpret every stored relation in a full model. -/
def denote (definitions : Definitions) (model : Model) :
    DefinitionEnv model.toPreModel definitions.signatures :=
  definitions.data.denote model

/-- Expose the stored-body meaning of one typed definition. -/
def definitionBody (definitions : Definitions) (pre : PreModel)
    (env : DefinitionEnv pre definitions.signatures)
    (reference : DefVar definitions.signatures args) :
    PreModel.Args pre.Domain args → Prop :=
  definitions.data.bodyMeaning pre env reference

/-- Full-model definition meaning, computed from the exact stored dependency chain. -/
def denoteDefinition (definitions : Definitions) (model : Model)
    (reference : DefVar definitions.signatures args) :
    PreModel.Args model.toPreModel.Domain args → Prop :=
  definitions.definitionBody model.toPreModel
    (definitions.denote model) reference

/-- Recursive full-model interpretation satisfies every stored definition. -/
theorem denote_lawful (definitions : Definitions) (model : Model) :
    DefinitionLawful model.toPreModel definitions
      (definitions.denote model) :=
  definitions.data.denote_lawful model

/-- Lookup computes to the exact recursively denoted stored body. -/
theorem lookup_denote (definitions : Definitions) (model : Model)
    (reference : DefVar definitions.signatures args) :
    DefinitionEnv.lookup (definitions.denote model) reference =
      definitions.denoteDefinition model reference := by
  funext values
  apply propext
  exact definitions.data.lookup_iff_body
    (definitions.denote model)
    (definitions.denote_lawful model) reference values

/-- The newest full-model entry is its open body over the prior interpretation. -/
@[simp] theorem denote_snoc_newest
    (priorDefs : Definitions) (args : List Sig)
    (body : OpenDiagram priorDefs.signatures args) (model : Model) :
    DefinitionEnv.lookup ((snoc priorDefs args body).denote model)
        (newest priorDefs args body) =
      fun values =>
        denoteOpen model.toPreModel (priorDefs.denote model) body values :=
  by
    rfl

/-- Snoc preserves every earlier interpretation exactly. -/
@[simp] theorem denote_snoc_earlier
    (priorDefs : Definitions) (newArgs : List Sig)
    (body : OpenDiagram priorDefs.signatures newArgs) (model : Model)
    (reference : DefVar priorDefs.signatures args) :
    DefinitionEnv.lookup ((snoc priorDefs newArgs body).denote model)
        (weaken priorDefs newArgs body reference) =
      DefinitionEnv.lookup (priorDefs.denote model) reference :=
  by
    rfl

/-- Any lawful generic interpretation exposes the exact stored-body equation. -/
theorem lawful_lookup_iff
    (definitions : Definitions) (pre : PreModel)
    (env : DefinitionEnv pre definitions.signatures)
    (lawful : DefinitionLawful pre definitions env)
    (reference : DefVar definitions.signatures args)
    (values : PreModel.Args pre.Domain args) :
    DefinitionEnv.lookup env reference values ↔
      definitions.definitionBody pre env reference values :=
  definitions.data.lookup_iff_body env lawful reference values

/--
Generic definitional transparency: a named item denotes exactly its stored body
under any lawful premodel interpretation.
-/
theorem named_iff_definition
    (definitions : Definitions) (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions.signatures)
    (lawful : DefinitionLawful pre definitions definitionEnv)
    (wireEnv : Env pre ctx)
    (reference : DefVar definitions.signatures args)
    (arguments : Vars ctx args) :
    denoteItem pre definitionEnv wireEnv (.named reference arguments) ↔
      definitions.definitionBody pre definitionEnv reference
        (Vars.denote wireEnv arguments) := by
  rw [denoteItem_named]
  exact definitions.lawful_lookup_iff pre definitionEnv lawful reference
    (Vars.denote wireEnv arguments)

/-- Generic unfold direction; no full-model representability premise is used. -/
theorem unfold_named
    (definitions : Definitions) (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions.signatures)
    (lawful : DefinitionLawful pre definitions definitionEnv)
    (wireEnv : Env pre ctx)
    (reference : DefVar definitions.signatures args)
    (arguments : Vars ctx args)
    (namedDenotes :
      denoteItem pre definitionEnv wireEnv (.named reference arguments)) :
    definitions.definitionBody pre definitionEnv reference
      (Vars.denote wireEnv arguments) :=
  (definitions.named_iff_definition pre definitionEnv lawful wireEnv
    reference arguments).mp namedDenotes

/-- Generic fold direction; no full-model representability premise is used. -/
theorem fold_named
    (definitions : Definitions) (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions.signatures)
    (lawful : DefinitionLawful pre definitions definitionEnv)
    (wireEnv : Env pre ctx)
    (reference : DefVar definitions.signatures args)
    (arguments : Vars ctx args)
    (bodyDenotes :
      definitions.definitionBody pre definitionEnv reference
        (Vars.denote wireEnv arguments)) :
    denoteItem pre definitionEnv wireEnv (.named reference arguments) :=
  (definitions.named_iff_definition pre definitionEnv lawful wireEnv
    reference arguments).mpr bodyDenotes

end Definitions

/-- Conjunction storage order has no semantic effect. -/
theorem denoteItemSeq_append_comm
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (env : Env pre ctx) (left right : ItemSeq defs ctx) :
    denoteItemSeq pre definitions env (left.append right) ↔
      denoteItemSeq pre definitions env (right.append left) := by
  rw [denoteItemSeq_append, denoteItemSeq_append]
  exact and_comm

namespace OpenDiagram

/-- Replace only the intrinsic body, preserving boundary identity and order. -/
def withBody (diagram : OpenDiagram defs args)
    (body : Region defs diagram.classes) : OpenDiagram defs args :=
  { diagram with body := body }

/-- Open denotation is invariant under conjunction item order. -/
theorem denote_item_order
    (diagram : OpenDiagram defs args)
    (pre : PreModel) (definitions : DefinitionEnv pre defs)
    (left right : ItemSeq defs diagram.classes)
    (values : BoundaryEnv pre args) :
    denoteOpen pre definitions
        (diagram.withBody (.mk (left.append right))) values ↔
      denoteOpen pre definitions
        (diagram.withBody (.mk (right.append left))) values := by
  constructor
  · rintro ⟨env, boundary, body⟩
    refine ⟨env, boundary, ?_⟩
    exact (denoteItemSeq_append_comm pre definitions env left right).mp body
  · rintro ⟨env, boundary, body⟩
    refine ⟨env, boundary, ?_⟩
    exact (denoteItemSeq_append_comm pre definitions env right left).mp body

end OpenDiagram

/-! Executable ordered-definition acceptance examples. -/

example (definitions : Definitions) (model : Model)
    (reference : DefVar definitions.signatures args) :
    DefinitionEnv.lookup (definitions.denote model) reference =
      definitions.denoteDefinition model reference := by
  exact Definitions.lookup_denote definitions model reference

example (priorDefs : Definitions) (newArgs : List Sig)
    (body : OpenDiagram priorDefs.signatures newArgs) (model : Model)
    (reference : DefVar priorDefs.signatures args) :
    DefinitionEnv.lookup
        ((Definitions.snoc priorDefs newArgs body).denote model)
        (Definitions.weaken priorDefs newArgs body reference) =
      DefinitionEnv.lookup (priorDefs.denote model) reference := by
  exact Definitions.denote_snoc_earlier
    priorDefs newArgs body model reference

end VisualProof
