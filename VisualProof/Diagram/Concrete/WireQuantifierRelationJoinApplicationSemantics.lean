import VisualProof.Diagram.Concrete.WireQuantifierRelationJoinAlignment

namespace VisualProof

universe u

namespace WireQuantifierSemantics

/-- Concatenate two heterogeneous premodel tuples without changing entries. -/
def appendArgs
    {Domain : Sig → Type u} :
    {left : List Sig} →
      PreModel.Args Domain left →
      PreModel.Args Domain right →
      PreModel.Args Domain (left ++ right)
  | [], PUnit.unit, suffix => suffix
  | _ :: _, ⟨head, tail⟩, suffix =>
      ⟨head, appendArgs tail suffix⟩

/--
The relation value denoted by checked-open content after fixing its ambient
parameter tuple.
-/
def contentRelation
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {args parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs) :
    Sig.denote model.Carrier (.rel args) :=
  fun formalValues =>
    denoteOpen model.toPreModel definitionEnv contentCompiled.openDiagram
      (boundaryExact.symm ▸
        appendArgs (PreModel.Args.ofFull formalValues) parameterValues)

/--
Applying the canonical relation represented by checked-open content unfolds
to that content with the supplied formal tuple followed by its fixed
parameter tuple.
-/
theorem contentRelation_applies
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {args parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (formalValues :
      PreModel.Args model.toPreModel.Domain args) :
    model.toPreModel.apply
        (contentRelation model definitionEnv contentCompiled
          boundaryExact parameterValues)
        formalValues ↔
      denoteOpen model.toPreModel definitionEnv
        contentCompiled.openDiagram
        (boundaryExact.symm ▸
          appendArgs formalValues parameterValues) := by
  simp [Model.toPreModel, contentRelation]

end WireQuantifierSemantics

namespace ConcreteWireQuantifier

namespace RelationJoinSemantics

open Internal
open Internal.RelationJoinStep

private theorem castCompiledAtom
    {definitions : List (List Sig)}
    {diagram : ConcreteDiagram definitions.length}
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (node : diagram.NodeId)
    (args : List Sig)
    (head : Var left.sigs (.rel args))
    (arguments : Vars left.sigs args)
    (headWire : diagram.WireId)
    (argumentWires : List diagram.WireId)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram left [node] =
        some (.cons (.atom head arguments) .nil))
    (headOrigin :
      ConcreteElaboration.WireContext.origin diagram left.ids head =
        headWire)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins diagram left arguments =
        argumentWires) :
    ∃ (castHead : Var right.sigs (.rel args))
      (castArguments : Vars right.sigs args),
      ConcreteElaboration.compileNodes? definitions diagram right [node] =
        some (.cons (.atom castHead castArguments) .nil) ∧
      ConcreteElaboration.WireContext.origin diagram right.ids castHead =
        headWire ∧
      ConcreteElaboration.variableOrigins diagram right castArguments =
        argumentWires := by
  cases same
  exact ⟨head, arguments, compiled, headOrigin, argumentOrigins⟩

/--
The accepted application remains the same ordered atom in the relative frame
at the dying scope.
-/
theorem Internal.RelationJoinStep.relativeCompiledApplication
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {outer : ConcreteElaboration.WireContext step.prior.val}
    (relative : RegionFrame definitions step.prior.val outer)
    (relativeVisible :
      relative.visible = step.priorSite.frame.visible) :
    ∃ (head : Var relative.visible.sigs (.rel step.relationArgs))
      (arguments : Vars relative.visible.sigs step.relationArgs),
      ConcreteElaboration.compileNodes? definitions step.prior.val
          relative.visible [step.priorApplication] =
        some (.cons (.atom head arguments) .nil) ∧
      ConcreteElaboration.WireContext.origin step.prior.val
          relative.visible.ids head =
        step.priorWireImage dying ∧
      ConcreteElaboration.variableOrigins step.prior.val
          relative.visible arguments =
        step.priorArguments := by
  obtain ⟨applicationOuter, applicationVisible, head, arguments,
      compiled, headOrigin, argumentOrigins⟩ :=
    SingletonRemovalSemantics.RelationJoinStep.compiledApplication step
  exact
    castCompiledAtom
      (applicationVisible.symm.trans relativeVisible.symm)
      step.priorApplication step.relationArgs head arguments
      (step.priorWireImage dying) step.priorArguments
      compiled headOrigin argumentOrigins

/--
Transport the rule-owned source parameter-scope premise through the step's
sole region and wire images. No caller supplies an intermediate scope proof.
-/
theorem Internal.RelationJoinStep.priorParameterScopes
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (parameterScopes :
      ∀ position : Fin step.sourceParameters.length,
        source.val.Encloses
          (source.val.wires
            (step.sourceParameters.get position)).scope
          (source.val.wires dying).scope) :
    ∀ position : Fin step.sourceParameters.length,
      step.prior.val.Encloses
        (step.prior.val.wires
          (step.priorWireImage
            (step.sourceParameters.get position))).scope
        (step.prior.val.wires (step.priorWireImage dying)).scope := by
  intro position
  rw [step.priorWireScopeExact, step.priorWireScopeExact]
  exact
    (step.priorRegionImageEncloses
      (source.val.wires (step.sourceParameters.get position)).scope
      (source.val.wires dying).scope).2
      (parameterScopes position)

def Internal.variableOfMember
    (diagram : ConcreteDiagram definitionCount) :
    (ids : List diagram.WireId) →
      (wire : diagram.WireId) →
      wire ∈ ids →
      Var (ids.map fun candidate => (diagram.wires candidate).sig)
        (diagram.wires wire).sig
  | [], _, member => False.elim (by simpa using member)
  | head :: tail, wire, member =>
      if same : wire = head then
        same ▸ Var.here
      else
        .there
          (variableOfMember diagram tail wire
            ((List.mem_cons.mp member).resolve_left same))

theorem Internal.variableOfMember_origin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (wire : diagram.WireId)
    (member : wire ∈ ids) :
    ConcreteElaboration.WireContext.origin diagram ids
        (variableOfMember diagram ids wire member) =
      wire := by
  induction ids generalizing wire with
  | nil => simp at member
  | cons head tail induction =>
      simp only [variableOfMember]
      split
      · rename_i same
        subst wire
        rfl
      · rename_i different
        exact
          induction wire
            ((List.mem_cons.mp member).resolve_left different)

def Internal.variablesOfMembers
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram) :
    (wires : List diagram.WireId) →
      (∀ wire, wire ∈ wires → wire ∈ context.ids) →
      Vars context.sigs
        (wires.map fun wire => (diagram.wires wire).sig)
  | [], _ => .nil
  | head :: tail, members =>
      .cons
        (variableOfMember diagram context.ids head
          (members head (by simp)))
        (variablesOfMembers diagram context tail
          (fun wire member => members wire (by simp [member])))

theorem Internal.variablesOfMembers_origins
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (wires : List diagram.WireId)
    (members : ∀ wire, wire ∈ wires → wire ∈ context.ids) :
    ConcreteElaboration.variableOrigins diagram context
        (variablesOfMembers diagram context wires members) =
      wires := by
  induction wires generalizing context with
  | nil => rfl
  | cons head tail induction =>
      change
        ConcreteElaboration.WireContext.origin diagram context.ids
              (variableOfMember diagram context.ids head
                (members head (by simp))) ::
            ConcreteElaboration.variableOrigins diagram context
              (variablesOfMembers diagram context tail
                (fun wire member => members wire (by simp [member]))) =
          head :: tail
      rw [variableOfMember_origin]
      exact
        congrArg (List.cons head)
          (induction context
            (fun wire member => members wire (by simp [member])))

theorem Internal.variableOrigins_rename_mapped
    (sourceDiagram : ConcreteDiagram sourceDefinitionCount)
    (targetDiagram : ConcreteDiagram targetDefinitionCount)
    (sourceContext : ConcreteElaboration.WireContext sourceDiagram)
    (targetContext : ConcreteElaboration.WireContext targetDiagram)
    (rho : WireRenaming sourceContext.sigs targetContext.sigs)
    (sourceMap : α → sourceDiagram.WireId)
    (targetMap : α → targetDiagram.WireId)
    (action :
      ∀ (key : α) {sig : Sig}
        (value : Var sourceContext.sigs sig),
        ConcreteElaboration.WireContext.origin sourceDiagram
            sourceContext.ids value = sourceMap key →
          ConcreteElaboration.WireContext.origin targetDiagram
              targetContext.ids (rho value) = targetMap key)
    (variables : Vars sourceContext.sigs args)
    (keys : List α)
    (origins :
      ConcreteElaboration.variableOrigins sourceDiagram sourceContext
          variables =
        keys.map sourceMap) :
    ConcreteElaboration.variableOrigins targetDiagram targetContext
        (Vars.rename rho variables) =
      keys.map targetMap := by
  induction variables generalizing keys with
  | nil =>
      cases keys with
      | nil => rfl
      | cons key keys =>
          simp only [List.map_cons] at origins
          contradiction
  | cons value values induction =>
      cases keys with
      | nil =>
          simp only [List.map_nil] at origins
          contradiction
      | cons key keys =>
          simp only [ConcreteElaboration.variableOrigins, List.map_cons,
            List.cons.injEq] at origins
          change
            ConcreteElaboration.WireContext.origin targetDiagram
                targetContext.ids (rho value) ::
                  ConcreteElaboration.variableOrigins targetDiagram
                    targetContext (Vars.rename rho values) =
              targetMap key :: keys.map targetMap
          rw [action key value origins.1]
          exact congrArg (List.cons (targetMap key))
            (induction keys origins.2)

theorem Internal.RelationJoinStep.baseRegionImage_injective
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content) :
    Function.Injective step.baseRegionImage := by
  intro left right same
  rw [step.baseRegionImageExact, step.baseRegionImageExact] at same
  have erasedSame :
      ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication (step.priorRegionImage left) =
        ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion
          step.prior step.priorApplication
          (step.priorRegionImage right) := by
    exact checkedRegion_injective step.base_generated same
  have priorSame :=
    ConcreteDiagram.IdentityNormalizationCore.eraseNodeRegion_injective
      step.prior step.priorApplication erasedSame
  have leftRight :
      source.val.Encloses left right := by
    apply
      (step.priorRegionImageEncloses left right).mp
    simpa [priorSame] using
      step.prior.val.encloses_refl (step.priorRegionImage right)
  have rightLeft :
      source.val.Encloses right left := by
    apply
      (step.priorRegionImageEncloses right left).mp
    simpa [priorSame] using
      step.prior.val.encloses_refl (step.priorRegionImage left)
  exact
    InsertionCompilation.NaturalityInternal.checked_encloses_antisymm
      definitions source.val source.property leftRight rightLeft

theorem Internal.transport_context_sigs
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left) :
    (same ▸ context).sigs = context.sigs := by
  cases same
  rfl

private theorem transport_extended_context_sigs
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (region : left.RegionId) :
    ((same ▸ context).extend (same ▸ region)).sigs =
      (context.extend region).sigs := by
  cases same
  rfl

theorem Internal.transport_extended_context
    {definitionCount : Nat}
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (region : left.RegionId) :
    (same ▸ context).extend (same ▸ region) =
      same ▸ context.extend region := by
  cases same
  rfl

def Internal.transportVariables
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (variables : Vars context.sigs args) :
    Vars rightContext.sigs args :=
  congrArg ConcreteElaboration.WireContext.sigs contextExact ▸
    (transport_context_sigs same context).symm ▸ variables

def Internal.transportVariable
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    Var rightContext.sigs sig :=
  congrArg ConcreteElaboration.WireContext.sigs contextExact ▸
    (transport_context_sigs same context).symm ▸ value

theorem Internal.transportVariables_cons
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (head : Var context.sigs sig)
    (tail : Vars context.sigs args) :
    transportVariables same context rightContext contextExact
        (.cons head tail) =
      .cons
        (transportVariable same context rightContext contextExact head)
        (transportVariables same context rightContext contextExact tail) := by
  cases same
  cases contextExact
  rfl

theorem Internal.transportVariable_origin
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    ConcreteElaboration.WireContext.origin right rightContext.ids
        (transportVariable same context rightContext contextExact value) =
      Fin.cast (congrArg ConcreteDiagram.wireCount same)
        (ConcreteElaboration.WireContext.origin left context.ids value) := by
  cases same
  cases contextExact
  rfl

theorem Internal.transportVariable_heq
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    HEq
      (transportVariable same context rightContext contextExact value)
      value := by
  cases same
  cases contextExact
  rfl

def Internal.transportCheckedVariable
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val)
    (rightContext : ConcreteElaboration.WireContext right.val)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    Var rightContext.sigs sig := by
  cases same
  exact transportVariable rfl context rightContext contextExact value

theorem Internal.transportCheckedVariable_origin
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val)
    (rightContext : ConcreteElaboration.WireContext right.val)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    ConcreteElaboration.WireContext.origin right.val rightContext.ids
        (transportCheckedVariable same context rightContext contextExact
          value) =
      Fin.cast
        (congrArg ConcreteDiagram.wireCount
          (congrArg
            (fun checked : CheckedDiagram definitions => checked.val)
            same))
        (ConcreteElaboration.WireContext.origin left.val context.ids
          value) := by
  cases same
  cases contextExact
  rfl

theorem Internal.transportCheckedVariable_heq
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val)
    (rightContext : ConcreteElaboration.WireContext right.val)
    (contextExact : same ▸ context = rightContext)
    (value : Var context.sigs sig) :
    HEq
      (transportCheckedVariable same context rightContext contextExact value)
      value := by
  cases same
  cases contextExact
  rfl

theorem Internal.origin_cast_context
    (diagram : ConcreteDiagram definitionCount)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    {sig : Sig}
    (value : Var left.sigs sig) :
    ConcreteElaboration.WireContext.origin diagram right.ids
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ value) =
      ConcreteElaboration.WireContext.origin diagram left.ids value := by
  cases same
  rfl

theorem Internal.variableOrigins_cast_context
    (diagram : ConcreteDiagram definitionCount)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (values : Vars left.sigs args) :
    ConcreteElaboration.variableOrigins diagram right
        (congrArg ConcreteElaboration.WireContext.sigs same ▸ values) =
      ConcreteElaboration.variableOrigins diagram left values := by
  cases same
  rfl

theorem Internal.cast_variable_heq
    {left right : List Sig}
    (same : left = right)
    (value : Var left sig) :
    HEq (same ▸ value) value := by
  cases same
  rfl

theorem Internal.cast_renaming_roundtrip
    {left right source : List Sig}
    (same : left = right)
    (rho : WireRenaming source right)
    {sig : Sig}
    (value : Var source sig) :
    same ▸ ((same.symm ▸ rho) value) = rho value := by
  cases same
  rfl

theorem Internal.cast_renaming_variables_heq
    {left right source args : List Sig}
    (same : left = right)
    (rho : WireRenaming source left)
    (values : Vars source args) :
    HEq (Vars.rename (same ▸ rho) values) (Vars.rename rho values) := by
  cases same
  rfl

theorem Internal.cast_variables_heq
    {left right args : List Sig}
    (same : left = right)
    (values : Vars left args) :
    HEq (same ▸ values) values := by
  cases same
  rfl

theorem Internal.cast_environment_variables_denote
    {left right args : List Sig}
    (same : left = right)
    (env : Env pre left)
    (values : Vars left args) :
    Vars.denote (same ▸ env) (same ▸ values) =
      Vars.denote env values := by
  cases same
  rfl

theorem Internal.origin_cast_renaming
    (diagram : ConcreteDiagram definitionCount)
    {left right : ConcreteElaboration.WireContext diagram}
    (same : left = right)
    (sourceContext : List Sig)
    (rho : WireRenaming sourceContext left.sigs)
    {sig : Sig}
    (value : Var sourceContext sig) :
    ConcreteElaboration.WireContext.origin diagram right.ids
        ((congrArg ConcreteElaboration.WireContext.sigs same ▸ rho) value) =
      ConcreteElaboration.WireContext.origin diagram left.ids
        (rho value) := by
  cases same
  rfl

theorem Internal.extendedContextRenaming_origin
    (source : CheckedDiagram definitions)
    (removed : source.val.NodeId)
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    {sig : Sig}
    (value : Var (context.extend region).sigs sig) :
    ConcreteElaboration.WireContext.origin
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          source removed)
        ((SingletonRemovalSemantics.targetContext source removed context).extend
          (SingletonRemovalSemantics.targetRegion source removed region)).ids
        (SingletonRemovalSemantics.extendedContextRenaming source removed
          context region value) =
      SingletonRemovalSemantics.targetWire source removed
        (ConcreteElaboration.WireContext.origin source.val
          (context.extend region).ids value) := by
  unfold SingletonRemovalSemantics.extendedContextRenaming
  rw [origin_cast_renaming
    (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
      source removed)
    (SingletonRemovalSemantics.targetContext_extend source removed
      context region)
    (context.extend region).sigs
    (SingletonRemovalSemantics.contextRenaming source removed
      (context.extend region))]
  exact
    SingletonRemovalSemantics.contextRenaming_action source removed
      (context.extend region) value

def Internal.transportRenaming
    {source source' target target' : List Sig}
    (sourceExact : source = source')
    (targetExact : target = target')
    (rho : WireRenaming source' target') :
    WireRenaming source target :=
  fun {_} value => targetExact.symm ▸ rho (sourceExact ▸ value)

theorem Internal.transportRenaming_transportCheckedVariable
    {definitions : List (List Sig)}
    {left right : CheckedDiagram definitions}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left.val)
    (sourceContext : List Sig)
    (rho : WireRenaming sourceContext context.sigs)
    {sig : Sig}
    (value : Var sourceContext sig) :
    transportRenaming rfl
        (transport_checked_context_sigs same context) rho value =
      transportCheckedVariable same context
        (transportCheckedContext same context)
        (transport_checked_context_cast_eq same context)
        (rho value) := by
  cases same
  rfl

def Internal.embedOuterThroughSite
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (visible outer : ConcreteElaboration.WireContext base.val)
    (same : visible = outer.extend site) :
    WireRenaming outer.sigs visible.sigs :=
  fun {_} value =>
    (congrArg ConcreteElaboration.WireContext.sigs
      same).symm ▸
        ConcreteElaboration.appendRightVar base.val
          (base.val.wiresAt site) value

/-- Embed the canonical site-outer variables through the site's local block. -/
def aboveScopeEmbedOuter
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled) :
    WireRenaming canonical.siteOuter.sigs compiled.frame.visible.sigs :=
  embedOuterThroughSite compiled.frame.visible canonical.siteOuter
    canonical.visibleExact

private theorem embedOuterThroughSite_origin
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (visible outer : ConcreteElaboration.WireContext base.val)
    (same : visible = outer.extend site)
    {sig : Sig}
    (value : Var outer.sigs sig) :
    ConcreteElaboration.WireContext.origin base.val visible.ids
        (embedOuterThroughSite visible outer same value) =
      ConcreteElaboration.WireContext.origin base.val outer.ids value := by
  cases same
  simpa [embedOuterThroughSite, ConcreteElaboration.WireContext.extend]
    using
      (ConcreteElaboration.origin_appendRightVar base.val
        (base.val.wiresAt site) value)

theorem Internal.aboveScopeEmbedOuter_origin
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {compiled : SiteCompilation base site}
    (canonical : SiteCompilation.AboveScopeDecomposition compiled)
    {sig : Sig}
    (value : Var canonical.siteOuter.sigs sig) :
    ConcreteElaboration.WireContext.origin base.val
        compiled.frame.visible.ids
        (aboveScopeEmbedOuter canonical value) =
      ConcreteElaboration.WireContext.origin base.val
        canonical.siteOuter.ids value := by
  exact
    embedOuterThroughSite_origin compiled.frame.visible
      canonical.siteOuter canonical.visibleExact value

theorem Internal.transportRenaming_reindexed_identity
    {source source' target target' : List Sig}
    (sourceExact : source = source')
    (targetExact : target = target')
    (rawTargetToSource : target' = source')
    (targetToSource : target = source)
    (rho : WireRenaming source' target')
    (rawIdentity :
      (fun {sig} (value : Var source' sig) =>
        rawTargetToSource ▸ rho value) =
        (fun {_} (value : Var source' _) => value)) :
    (fun {sig} (value : Var source sig) =>
      targetToSource ▸
        transportRenaming sourceExact targetExact rho value) =
      (fun {_} (value : Var source _) => value) := by
  cases sourceExact
  cases targetExact
  have proofExact : targetToSource = rawTargetToSource :=
    Subsingleton.elim _ _
  rw [proofExact]
  exact rawIdentity

theorem Internal.envComp_transportRenaming
    {source source' target target' : List Sig}
    (sourceExact : source' = source)
    (targetExact : target' = target)
    (rho : WireRenaming source' target') :
    (fun (pre : PreModel.{u}) (env : Env pre target) =>
      sourceExact ▸ Env.comp (targetExact.symm ▸ env) rho) =
      (fun (pre : PreModel.{u}) (env : Env pre target) =>
        Env.comp env
          (transportRenaming sourceExact.symm targetExact.symm rho)) := by
  cases sourceExact
  cases targetExact
  rfl

theorem Internal.composeRenaming_reindexed_identity
    {source middle target : List Sig}
    (middleToSource : middle = source)
    (targetToMiddle : target = middle)
    (sourceToMiddle : WireRenaming source middle)
    (middleToTarget : WireRenaming middle target)
    (sourceToMiddleIdentity :
      (fun {sig} (value : Var source sig) =>
        middleToSource ▸ sourceToMiddle value) =
        (fun {_} (value : Var source _) => value))
    (middleToTargetIdentity :
      (fun {sig} (value : Var middle sig) =>
        targetToMiddle ▸ middleToTarget value) =
        (fun {_} (value : Var middle _) => value)) :
    (fun {sig} (value : Var source sig) =>
      targetToMiddle.trans middleToSource ▸
        middleToTarget (sourceToMiddle value)) =
      (fun {_} (value : Var source _) => value) := by
  cases middleToSource
  cases targetToMiddle
  have sourceExact :
      (sourceToMiddle : WireRenaming source source) =
        ((fun {_} (value : Var source _) => value) :
          WireRenaming source source) :=
    sourceToMiddleIdentity
  have targetExact :
      (middleToTarget : WireRenaming source source) =
        ((fun {_} (value : Var source _) => value) :
          WireRenaming source source) :=
    middleToTargetIdentity
  funext sig value
  have sourcePoint :=
    congrFun (congrFun sourceExact sig) value
  have targetPoint :=
    congrFun (congrFun targetExact sig) value
  simpa using
    (congrArg (fun mapped => middleToTarget mapped) sourcePoint).trans
      targetPoint

noncomputable def Internal.transportComposableSemanticZipperTargetHole
    {definitions : List (List Sig)}
    {sourceHole leftHole rightHole : List Sig}
    (same : leftHole = rightHole)
    (source : DiagramContext definitions sourceHole [])
    (target : DiagramContext definitions rightHole [])
    (rho : WireRenaming sourceHole rightHole)
    (outerMap :
      ∀ pre : PreModel.{u}, Env pre [] → Env pre [])
    (zipper :
      DiagramContext.ComposableSemanticZipper.{u} source target outerMap
        (fun (_pre : PreModel.{u}) env => Env.comp env rho)) :
    DiagramContext.ComposableSemanticZipper.{u} source (same.symm ▸ target)
      outerMap
      (fun (_pre : PreModel.{u}) env =>
        Env.comp env (transportRenaming rfl same rho)) := by
  cases same
  exact zipper

def Internal.transportEnvironment
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (env : Env pre context.sigs) :
    Env pre rightContext.sigs :=
  congrArg ConcreteElaboration.WireContext.sigs contextExact ▸
    (transport_context_sigs same context).symm ▸ env

theorem Internal.transportEnvironment_apply
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (env : Env pre context.sigs)
    (value : Var context.sigs sig) :
    transportEnvironment same context rightContext contextExact env sig
        (transportVariable same context rightContext contextExact value) =
      env sig value := by
  cases same
  cases contextExact
  rfl

theorem Internal.transportEnvironment_denote
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (env : Env pre context.sigs)
    (variables : Vars context.sigs args) :
    Vars.denote
        (transportEnvironment same context rightContext contextExact env)
        (transportVariables same context rightContext contextExact variables) =
      Vars.denote env variables := by
  cases same
  cases contextExact
  rfl

def Internal.untransportRegion
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (body : Region definitions rightContext.sigs) :
    Region definitions context.sigs :=
  transport_context_sigs same context ▸
    congrArg ConcreteElaboration.WireContext.sigs contextExact.symm ▸ body

private theorem untransportRegion_denotes
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs)
    (body : Region definitions rightContext.sigs) :
    denoteRegion pre definitionEnv env
        (untransportRegion same context rightContext contextExact body) ↔
      denoteRegion pre definitionEnv
        (transportEnvironment same context rightContext contextExact env)
        body := by
  cases same
  cases contextExact
  rfl

theorem Internal.denoteRegion_transport
    {left right : List Sig}
    (same : left = right)
    (pre : PreModel)
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre left)
    (body : Region definitions left) :
    denoteRegion pre definitionEnv env body ↔
      denoteRegion pre definitionEnv
        (same ▸ env) (same ▸ body) := by
  cases same
  rfl

theorem Internal.cast_region_trans
    {left middle right : List Sig}
    (first : left = middle)
    (second : middle = right)
    (body : Region definitions left) :
    (first.trans second) ▸ body =
      second ▸ first ▸ body := by
  cases first
  cases second
  rfl

theorem Internal.cast_region_eq
    {left right : List Sig}
    (same : left = right)
    (body : Region definitions left) :
    same ▸ body =
      cast (congrArg (Region definitions) same) body := by
  cases same
  rfl

theorem Internal.cast_region_heq
    {left right : List Sig}
    (same : left = right)
    (body : Region definitions left) :
    HEq (same ▸ body) body := by
  cases same
  rfl

theorem Internal.cast_env_apply
    {left right : List Sig}
    (same : left = right)
    (env : Env pre left)
    {sig : Sig}
    (value : Var left sig) :
    (same ▸ env) sig (same ▸ value) = env sig value := by
  cases same
  rfl

theorem Internal.transportVariables_origins
    {left right : ConcreteDiagram definitionCount}
    (same : left = right)
    (context : ConcreteElaboration.WireContext left)
    (rightContext : ConcreteElaboration.WireContext right)
    (contextExact : same ▸ context = rightContext)
    (variables : Vars context.sigs args) :
    ConcreteElaboration.variableOrigins right rightContext
        (transportVariables same context rightContext contextExact variables) =
      (ConcreteElaboration.variableOrigins left context variables).map
        fun wire =>
          Fin.cast (congrArg ConcreteDiagram.wireCount same) wire := by
  cases same
  cases contextExact
  change
    ConcreteElaboration.variableOrigins left context
        (transportVariables rfl context context rfl variables) =
      (ConcreteElaboration.variableOrigins left context variables).map
        (fun wire => Fin.cast rfl wire)
  rw [show transportVariables rfl context context rfl variables = variables
    by rfl]
  have castIdentity :
      (fun wire : left.WireId => Fin.cast rfl wire) = id := by
    funext wire
    rfl
  rw [castIdentity, List.map_id]

def Internal.RelationJoinStep.baseRenamedVariables
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {args : List Sig}
    (context : ConcreteElaboration.WireContext step.prior.val)
    (baseVisible : ConcreteElaboration.WireContext step.base.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        baseVisible)
    (variables : Vars context.sigs args) :
    Vars baseVisible.sigs args :=
  transportVariables step.base_generated.symm
    (SingletonRemovalSemantics.targetContext step.prior
      step.priorApplication context)
    baseVisible visibleExact
    (Vars.rename
        (SingletonRemovalSemantics.contextRenaming step.prior
          step.priorApplication context)
        variables)

def Internal.RelationJoinStep.baseRenamedVariable
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (baseVisible : ConcreteElaboration.WireContext step.base.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        baseVisible)
    (value : Var context.sigs sig) :
    Var baseVisible.sigs sig :=
  transportVariable step.base_generated.symm
    (SingletonRemovalSemantics.targetContext step.prior
      step.priorApplication context)
    baseVisible visibleExact
    (SingletonRemovalSemantics.contextRenaming step.prior
      step.priorApplication context value)

theorem Internal.RelationJoinStep.baseRenamedVariables_origins
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {args : List Sig}
    (context : ConcreteElaboration.WireContext step.prior.val)
    (baseVisible : ConcreteElaboration.WireContext step.base.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        baseVisible)
    (variables : Vars context.sigs args) :
    ConcreteElaboration.variableOrigins step.base.val baseVisible
        (baseRenamedVariables step context baseVisible visibleExact variables) =
      (ConcreteElaboration.variableOrigins step.prior.val context variables).map
        fun wire =>
          Fin.cast
            (congrArg ConcreteDiagram.wireCount
              step.base_generated).symm
            (SingletonRemovalSemantics.targetWire step.prior
              step.priorApplication wire) := by
  rw [baseRenamedVariables, transportVariables_origins]
  induction variables with
  | nil => rfl
  | cons head tail induction =>
      simp only [Vars.rename, ConcreteElaboration.variableOrigins,
        List.map_cons, List.cons.injEq]
      constructor
      · apply congrArg
          (Fin.cast
            (congrArg ConcreteDiagram.wireCount
              step.base_generated).symm)
        exact
          SingletonRemovalSemantics.contextRenaming_action step.prior
            step.priorApplication context head
      · exact induction

theorem Internal.siteCompilation_visible_nodup
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    compiled.frame.visible.ids.Nodup := by
  obtain ⟨scopeCompiled, outer, _fuel, _relative, _relativeVisible,
      _inner, scopeVisible, _rootInner, above, _generated, _relativeBody,
      _relativeContext, _scopeBody, _rootBody, _replacementBody, _cutDepth⟩ :=
    compiled.factorAt_relative_origin site
      (ConcreteDiagram.encloses_refl base.val site)
  have same : scopeCompiled = compiled :=
    SiteCompilation.unique scopeCompiled compiled
  subst scopeCompiled
  rw [scopeVisible]
  exact
    ConcreteElaboration.extend_nodup definitions base.val base.property
      outer site above

private def formalVariables :
    (formals : List Sig) →
      {parameters : List Sig} →
      Vars context (formals ++ parameters) →
      Vars context formals
  | [], _, _ => .nil
  | _ :: rest, _, .cons head tail =>
      .cons head (formalVariables rest tail)

private theorem variableOrigins_eq_map_entries
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (variables : Vars context.sigs args) :
    ConcreteElaboration.variableOrigins diagram context variables =
      variables.entries.map fun packed =>
        match packed with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin diagram context.ids value := by
  induction variables with
  | nil => rfl
  | cons _ _ induction =>
      simp only [ConcreteElaboration.variableOrigins, Vars.entries,
        List.map_cons, induction]

theorem Internal.variableOrigins_cast
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    {left right : List Sig}
    (same : left = right)
    (variables : Vars context.sigs left) :
    ConcreteElaboration.variableOrigins diagram context (same ▸ variables) =
      ConcreteElaboration.variableOrigins diagram context variables := by
  cases same
  rfl

private theorem variableOrigins_length
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (variables : Vars context.sigs args) :
    (ConcreteElaboration.variableOrigins diagram context variables).length =
      args.length := by
  induction variables with
  | nil => rfl
  | cons _ _ induction =>
      simp only [ConcreteElaboration.variableOrigins, List.length_cons,
        induction]

private theorem List.get_cast_of_eq
    {left right : List α}
    (same : left = right)
    (position : Fin left.length) :
    left.get position =
      right.get (Fin.cast (congrArg List.length same) position) := by
  cases same
  rfl

private theorem variableOrigins_formalVariables
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (formals : List Sig)
    {parameters : List Sig}
    (variables : Vars context.sigs (formals ++ parameters)) :
    ConcreteElaboration.variableOrigins diagram context
        (formalVariables formals variables) =
      (ConcreteElaboration.variableOrigins diagram context variables).take
        formals.length := by
  induction formals with
  | nil => rfl
  | cons _ rest induction =>
      cases variables with
      | cons head tail =>
          change
            ConcreteElaboration.WireContext.origin diagram context.ids head ::
                ConcreteElaboration.variableOrigins diagram context
                  (formalVariables rest tail) =
              List.take (rest.length + 1)
                (ConcreteElaboration.WireContext.origin diagram context.ids head ::
                  ConcreteElaboration.variableOrigins diagram context tail)
          rw [show rest.length + 1 = Nat.succ rest.length by omega,
            List.take_succ_cons, induction tail]

theorem Internal.variables_eq_of_origins
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (nodup : context.ids.Nodup)
    (left right : Vars context.sigs args)
    (same :
      ConcreteElaboration.variableOrigins diagram context left =
        ConcreteElaboration.variableOrigins diagram context right) :
    left = right := by
  induction left with
  | nil =>
      cases right
      rfl
  | cons leftHead leftTail induction =>
      cases right with
      | cons rightHead rightTail =>
          simp only [ConcreteElaboration.variableOrigins, List.cons.injEq]
            at same
          have headExact :=
            InsertionCompilation.NaturalityInternal.origin_injective
              diagram context.ids nodup same.1
          subst rightHead
          exact congrArg (Vars.cons leftHead) (induction rightTail same.2)

private theorem insertion_target_position_origins
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {attachment : ConcreteSpliceAttachment base site fragment}
    (compiled : InsertionCompilation fragmentCompiled attachment) :
    ConcreteElaboration.variableOrigins base.val compiled.site.frame.visible
        compiled.intrinsicAttachment.positions =
      List.ofFn attachment.target := by
  rw [variableOrigins_eq_map_entries]
  apply List.ext_get
  · simp only [List.length_map, ExtractedBoundaryCompiler.entries_length,
      List.length_ofFn, checkedBoundarySigs, List.length_map]
  · intro position leftBound rightBound
    let boundaryPosition : Fin fragment.val.boundary.length :=
      ⟨position, by simpa using rightBound⟩
    have exactOrigin := compiled.targetPackedAt_origin boundaryPosition
    simpa only [InsertionCompilation.intrinsicAttachment,
      intrinsicAttachmentFromPositions, SpliceAttachment.positions,
      InsertionCompilation.targetPackedAt, VisualProof.targetPackedAt,
      List.get_eq_getElem, List.getElem_map, List.getElem_ofFn] using exactOrigin

private theorem RelationJoinStep.formalVariables_exact
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        compiled.site.frame.visible)
    (arguments : Vars context.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context arguments =
        step.priorArguments) :
    formalVariables step.relationArgs
        (boundaryExact ▸ compiled.intrinsicAttachment.positions) =
      baseRenamedVariables step context compiled.site.frame.visible
        visibleExact arguments := by
  apply
    variables_eq_of_origins step.base.val compiled.site.frame.visible
      (siteCompilation_visible_nodup compiled.site)
  rw [variableOrigins_formalVariables,
    variableOrigins_cast,
    insertion_target_position_origins compiled,
    Internal.RelationJoinStep.baseRenamedVariables_origins,
    argumentOrigins, step.priorArgumentsExact]
  have argumentLength :
      step.sourceArguments.length = step.relationArgs.length := by
    have sameLength := congrArg List.length argumentOrigins
    rw [step.priorArgumentsExact, List.length_map] at sameLength
    rw [variableOrigins_length] at sameLength
    exact sameLength.symm
  have boundaryLength :
      content.val.boundary.length =
        step.relationArgs.length + parameterSigs.length := by
    have sameLength := congrArg List.length boundaryExact
    simpa only [checkedBoundarySigs, List.length_map, List.length_append]
      using sameLength
  apply List.ext_get
  · simp only [List.length_take, List.length_ofFn, List.length_map]
    rw [boundaryLength, Nat.min_eq_left (by omega), argumentLength]
  · intro position leftBound rightBound
    have positionSource : position < step.sourceArguments.length := by
      simpa only [List.length_map] using rightBound
    let sourcePosition : Fin step.sourceArguments.length :=
      ⟨position, positionSource⟩
    let boundaryPosition : Fin content.val.boundary.length :=
      ⟨position, by
        rw [boundaryLength, ← argumentLength]
        omega⟩
    have targetExact := step.targetExact boundaryPosition
    have attachmentGet :
        step.sourceAttachments.get
            (Fin.cast step.sourceAttachmentArity.symm boundaryPosition) =
          step.sourceArguments.get sourcePosition := by
      calc
        _ =
            (step.sourceArguments ++ step.sourceParameters).get
              (Fin.cast
                (congrArg List.length step.sourceAttachmentsExact)
                (Fin.cast step.sourceAttachmentArity.symm
                  boundaryPosition)) :=
          List.get_cast_of_eq step.sourceAttachmentsExact _
        _ = step.sourceArguments.get sourcePosition := by
          have positionAppend :
              position <
                (step.sourceArguments ++ step.sourceParameters).length := by
            simp only [List.length_append]
            omega
          change
            (step.sourceArguments ++
                step.sourceParameters)[position]'positionAppend =
              step.sourceArguments[position]'positionSource
          exact List.getElem_append_left positionSource
    have rawBridge :=
      SingletonRemovalSemantics.RelationJoinStep.rawTargetWire_eq_baseWireImage
        step (step.sourceArguments.get sourcePosition)
    have targetFormal :
        step.attachment.target boundaryPosition =
          Fin.cast
            (congrArg ConcreteDiagram.wireCount
              step.base_generated).symm
            (SingletonRemovalSemantics.targetWire step.prior
              step.priorApplication
              (step.priorWireImage
                (step.sourceArguments.get sourcePosition))) := by
      exact
        (targetExact.trans
          (congrArg step.baseWireImage attachmentGet)).trans rawBridge.symm
    simpa only [List.get_eq_getElem, List.getElem_take, List.getElem_ofFn,
      List.getElem_map, Function.comp_apply] using targetFormal

def Internal.parameterVariables :
    (formals : List Sig) →
      {parameters : List Sig} →
      Vars context (formals ++ parameters) →
      Vars context parameters
  | [], _, variables => variables
  | _ :: rest, _, .cons _ tail =>
      parameterVariables rest tail

private theorem variableOrigins_parameterVariables
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (formals : List Sig)
    {parameters : List Sig}
    (variables : Vars context.sigs (formals ++ parameters)) :
    ConcreteElaboration.variableOrigins diagram context
        (parameterVariables formals variables) =
      (ConcreteElaboration.variableOrigins diagram context variables).drop
        formals.length := by
  induction formals with
  | nil => rfl
  | cons _ rest induction =>
      cases variables with
      | cons _ tail =>
          simpa [parameterVariables,
            ConcreteElaboration.variableOrigins] using induction tail

/--
The accepted boundary suffix is exactly the ordered source-parameter image in
the same canonical base visible context as the formal prefix.
-/
theorem Internal.RelationJoinStep.parameterVariables_exact
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        compiled.site.frame.visible)
    (arguments : Vars context.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context arguments =
        step.priorArguments)
    (parameters : Vars context.sigs parameterSigs)
    (parameterOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context parameters =
        step.sourceParameters.map step.priorWireImage) :
    parameterVariables step.relationArgs
        (boundaryExact ▸ compiled.intrinsicAttachment.positions) =
      baseRenamedVariables step context compiled.site.frame.visible
        visibleExact parameters := by
  apply
    variables_eq_of_origins step.base.val compiled.site.frame.visible
      (siteCompilation_visible_nodup compiled.site)
  rw [variableOrigins_parameterVariables, variableOrigins_cast,
    insertion_target_position_origins compiled,
    Internal.RelationJoinStep.baseRenamedVariables_origins, parameterOrigins]
  have argumentLength :
      step.sourceArguments.length = step.relationArgs.length := by
    have sameLength := congrArg List.length argumentOrigins
    rw [step.priorArgumentsExact, List.length_map] at sameLength
    rw [variableOrigins_length] at sameLength
    exact sameLength.symm
  have parameterLength :
      step.sourceParameters.length = parameterSigs.length := by
    have sameLength := congrArg List.length parameterOrigins
    rw [List.length_map] at sameLength
    rw [variableOrigins_length] at sameLength
    exact sameLength.symm
  have boundaryLength :
      content.val.boundary.length =
        step.relationArgs.length + parameterSigs.length := by
    have sameLength := congrArg List.length boundaryExact
    simpa only [checkedBoundarySigs, List.length_map, List.length_append]
      using sameLength
  apply List.ext_get
  · simp only [List.length_drop, List.length_ofFn, List.length_map]
    rw [boundaryLength, parameterLength]
    omega
  · intro position leftBound rightBound
    have parameterPosition : position < step.sourceParameters.length := by
      simpa only [List.length_map] using rightBound
    let sourcePosition : Fin step.sourceParameters.length :=
      ⟨position, parameterPosition⟩
    let boundaryPosition : Fin content.val.boundary.length :=
      ⟨step.relationArgs.length + position, by
        rw [boundaryLength]
        omega⟩
    have targetExact := step.targetExact boundaryPosition
    have attachmentGet :
        step.sourceAttachments.get
            (Fin.cast step.sourceAttachmentArity.symm boundaryPosition) =
          step.sourceParameters.get sourcePosition := by
      calc
        _ =
            (step.sourceArguments ++ step.sourceParameters).get
              (Fin.cast
                (congrArg List.length step.sourceAttachmentsExact)
                (Fin.cast step.sourceAttachmentArity.symm
                  boundaryPosition)) :=
          List.get_cast_of_eq step.sourceAttachmentsExact _
        _ = step.sourceParameters.get sourcePosition := by
          let sourceAppendPosition :
              Fin (step.sourceArguments ++
                step.sourceParameters).length :=
            ⟨step.sourceArguments.length + position, by
              simp only [List.length_append]
              omega⟩
          have indexExact :
              Fin.cast
                  (congrArg List.length step.sourceAttachmentsExact)
                  (Fin.cast step.sourceAttachmentArity.symm
                    boundaryPosition) =
                sourceAppendPosition := by
            apply Fin.ext
            change
              step.relationArgs.length + position =
                step.sourceArguments.length + position
            omega
          rw [indexExact]
          change
            (step.sourceArguments ++ step.sourceParameters).get
                sourceAppendPosition =
              step.sourceParameters.get sourcePosition
          simpa using
            (List.getElem_append_right
              (as := step.sourceArguments) (bs := step.sourceParameters)
              (i := step.sourceArguments.length + position) (by omega))
    have rawBridge :=
      SingletonRemovalSemantics.RelationJoinStep.rawTargetWire_eq_baseWireImage
        step (step.sourceParameters.get sourcePosition)
    have targetParameter :
        step.attachment.target boundaryPosition =
          Fin.cast
            (congrArg ConcreteDiagram.wireCount
              step.base_generated).symm
            (SingletonRemovalSemantics.targetWire step.prior
              step.priorApplication
              (step.priorWireImage
                (step.sourceParameters.get sourcePosition))) := by
      exact
        (targetExact.trans
          (congrArg step.baseWireImage attachmentGet)).trans rawBridge.symm
    simpa only [List.get_eq_getElem, List.getElem_drop, List.getElem_ofFn,
      List.getElem_map, Function.comp_apply] using targetParameter

theorem Internal.RelationJoinStep.priorParameterSignatures
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (arguments : Vars context.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context arguments =
        step.priorArguments) :
    step.sourceParameters.map
        (fun wire =>
          (step.prior.val.wires (step.priorWireImage wire)).sig) =
      parameterSigs := by
  have argumentLength :
      step.sourceArguments.length = step.relationArgs.length := by
    have sameLength := congrArg List.length argumentOrigins
    rw [step.priorArgumentsExact, List.length_map] at sameLength
    rw [variableOrigins_length] at sameLength
    exact sameLength.symm
  have boundaryLength :
      content.val.boundary.length =
        step.relationArgs.length + parameterSigs.length := by
    have sameLength := congrArg List.length boundaryExact
    simpa only [checkedBoundarySigs, List.length_map, List.length_append]
      using sameLength
  have parameterLength :
      step.sourceParameters.length = parameterSigs.length := by
    have attachmentsLength :=
      congrArg List.length step.sourceAttachmentsExact
    rw [List.length_append, step.sourceAttachmentArity,
      boundaryLength, argumentLength] at attachmentsLength
    omega
  apply List.ext_get
  · simpa only [List.length_map] using parameterLength
  · intro position leftBound rightBound
    let sourcePosition : Fin step.sourceParameters.length :=
      ⟨position, by simpa only [List.length_map] using leftBound⟩
    let boundaryPosition : Fin content.val.boundary.length :=
      ⟨step.relationArgs.length + position, by
        rw [boundaryLength]
        exact Nat.add_lt_add_left rightBound step.relationArgs.length⟩
    have targetExact := step.targetExact boundaryPosition
    have attachmentGet :
        step.sourceAttachments.get
            (Fin.cast step.sourceAttachmentArity.symm boundaryPosition) =
          step.sourceParameters.get sourcePosition := by
      calc
        _ =
            (step.sourceArguments ++ step.sourceParameters).get
              (Fin.cast
                (congrArg List.length step.sourceAttachmentsExact)
                (Fin.cast step.sourceAttachmentArity.symm
                  boundaryPosition)) :=
          List.get_cast_of_eq step.sourceAttachmentsExact _
        _ = step.sourceParameters.get sourcePosition := by
          let appendPosition :
              Fin (step.sourceArguments ++ step.sourceParameters).length :=
            ⟨step.sourceArguments.length + position, by
              simp only [List.length_append]
              omega⟩
          have indexExact :
              Fin.cast
                  (congrArg List.length step.sourceAttachmentsExact)
                  (Fin.cast step.sourceAttachmentArity.symm
                    boundaryPosition) =
                appendPosition := by
            apply Fin.ext
            change
              step.relationArgs.length + position =
                step.sourceArguments.length + position
            omega
          rw [indexExact]
          change
            (step.sourceArguments ++ step.sourceParameters).get
                appendPosition =
              step.sourceParameters.get sourcePosition
          simpa using
            (List.getElem_append_right
              (as := step.sourceArguments) (bs := step.sourceParameters)
              (i := step.sourceArguments.length + position) (by omega))
    have signatureAtTarget := step.attachment.signature boundaryPosition
    rw [targetExact, attachmentGet, ← step.baseWire_signature] at signatureAtTarget
    have signatureBoundary :
        (step.prior.val.wires
            (step.priorWireImage
              (step.sourceParameters.get sourcePosition))).sig =
          (checkedBoundarySigs content).get
            (Fin.cast
              (by simpa only [checkedBoundarySigs, List.length_map])
              boundaryPosition) := by
      simpa only [checkedBoundarySigs, List.get_eq_getElem,
        List.getElem_map] using signatureAtTarget
    have boundaryAt :=
      List.get_cast_of_eq boundaryExact
        (Fin.cast
          (by simpa only [checkedBoundarySigs, List.length_map])
          boundaryPosition)
    let suffixPosition : Fin parameterSigs.length := ⟨position, rightBound⟩
    let appendPosition :
        Fin (step.relationArgs ++ parameterSigs).length :=
      ⟨step.relationArgs.length + position, by
        simp only [List.length_append]
        omega⟩
    have boundaryIndexExact :
        Fin.cast (congrArg List.length boundaryExact)
            (Fin.cast
              (by simpa only [checkedBoundarySigs, List.length_map])
              boundaryPosition) =
          appendPosition := by
      apply Fin.ext
      rfl
    have boundarySuffix :
        (step.relationArgs ++ parameterSigs).get
            (Fin.cast (congrArg List.length boundaryExact)
              (Fin.cast
                (by simpa only [checkedBoundarySigs, List.length_map])
                boundaryPosition)) =
          parameterSigs.get suffixPosition := by
      rw [boundaryIndexExact]
      change
        (step.relationArgs ++ parameterSigs).get appendPosition =
          parameterSigs.get suffixPosition
      simpa using
        (List.getElem_append_right
          (as := step.relationArgs) (bs := parameterSigs)
          (i := step.relationArgs.length + position) (by omega))
    simpa only [List.get_eq_getElem, List.getElem_map, sourcePosition,
      suffixPosition] using
        signatureBoundary.trans (boundaryAt.trans boundarySuffix)

private theorem checkedEncloses_trans
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {outer middle inner : diagram.RegionId}
    (outerMiddle : diagram.Encloses outer middle)
    (middleInner : diagram.Encloses middle inner) :
    diagram.Encloses outer inner := by
  obtain ⟨outerSteps, outerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram outer middle).mp
      outerMiddle
  obtain ⟨innerSteps, innerClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists diagram middle inner).mp
      middleInner
  have combined :
      diagram.climb (innerSteps.val + outerSteps.val) inner =
        some outer := by
    rw [ConcreteDiagram.climb_add, innerClimb]
    exact outerClimb
  have bounded :=
    ConcreteElaboration.successfulClimb_le_count definitions diagram
      wellFormed (innerSteps.val + outerSteps.val) inner outer combined
  exact
    (ConcreteElaboration.encloses_iff_exists diagram outer inner).mpr
      ⟨⟨innerSteps.val + outerSteps.val, by omega⟩, combined⟩

private theorem RelationJoinStep.priorParameterVariables
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (parameterScopes :
      ∀ position : Fin step.sourceParameters.length,
        source.val.Encloses
          (source.val.wires
            (step.sourceParameters.get position)).scope
          (source.val.wires dying).scope)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (frame : RegionFrame definitions step.prior.val context)
    (frameVisible : frame.visible = step.priorSite.frame.visible)
    (arguments : Vars frame.visible.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val frame.visible
          arguments =
        step.priorArguments) :
    ∃ parameters : Vars frame.visible.sigs parameterSigs,
      ConcreteElaboration.variableOrigins step.prior.val frame.visible
          parameters =
        step.sourceParameters.map step.priorWireImage := by
  have signatures :=
    Internal.RelationJoinStep.priorParameterSignatures step boundaryExact frame.visible
      arguments argumentOrigins
  let wires := step.sourceParameters.map step.priorWireImage
  have members :
      ∀ wire, wire ∈ wires → wire ∈ frame.visible.ids := by
    intro wire member
    obtain ⟨sourceWire, sourceMember, rfl⟩ := List.mem_map.mp member
    have sourcePosition :=
      List.get_of_mem sourceMember
    obtain ⟨position, rfl⟩ := sourcePosition
    have parameterAboveDying :=
      Internal.RelationJoinStep.priorParameterScopes step parameterScopes position
    have dyingAboveSite :
        step.prior.val.Encloses
          (step.prior.val.wires (step.priorWireImage dying)).scope
          (step.priorRegionImage step.sourceRegion) := by
      rw [step.priorWireScopeExact]
      exact step.prior_dying_scope_encloses_site
    have parameterAboveSite :=
      checkedEncloses_trans definitions step.prior.val step.prior.property
        parameterAboveDying dyingAboveSite
    rw [frameVisible]
    exact
      step.priorSite.visible_of_encloses
        (step.priorWireImage (step.sourceParameters.get position))
        parameterAboveSite
  let native := variablesOfMembers step.prior.val frame.visible wires members
  let nativeSigs :=
    wires.map fun wire => (step.prior.val.wires wire).sig
  have nativeSigsExact : nativeSigs = parameterSigs := by
    unfold nativeSigs wires
    rw [List.map_map]
    exact signatures
  refine ⟨nativeSigsExact ▸ native, ?_⟩
  rw [variableOrigins_cast]
  exact variablesOfMembers_origins step.prior.val frame.visible wires members

private theorem denote_split_variables
    (env : Env pre context)
    (formals : List Sig)
    {parameters : List Sig}
    (variables : Vars context (formals ++ parameters)) :
    Vars.denote env variables =
      WireQuantifierSemantics.appendArgs
        (Vars.denote env (formalVariables formals variables))
        (Vars.denote env (parameterVariables formals variables)) := by
  induction formals with
  | nil => rfl
  | cons _ rest induction =>
      cases variables with
      | cons head tail =>
          simp only [Vars.denote_cons, formalVariables, parameterVariables,
            WireQuantifierSemantics.appendArgs]
          exact congrArg (fun value => (env _ head, value)) (induction tail)

private theorem boundary_values_from_formals
    (env : Env pre context)
    {boundary formals parameters : List Sig}
    (boundaryExact : boundary = formals ++ parameters)
    (positions : Vars context boundary)
    (arguments : Vars context formals)
    (formalExact :
      formalVariables formals (boundaryExact ▸ positions) = arguments) :
    Vars.denote env positions =
      boundaryExact.symm ▸
        WireQuantifierSemantics.appendArgs
          (Vars.denote env arguments)
          (Vars.denote env
            (parameterVariables formals (boundaryExact ▸ positions))) := by
  cases boundaryExact
  rw [denote_split_variables, formalExact]

/--
The canonical content relation replaces one compiled application exactly when
the accepted intrinsic boundary tuple is its ordered formal tuple followed by
the fixed parameter tuple.
-/
private theorem application_denotes_intrinsic
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {args parameterSigs context : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (env : Env model.toPreModel context)
    (head : Var context (.rel args))
    (arguments : Vars context args)
    (attachment :
      SpliceAttachment contentCompiled.openDiagram context)
    (headValue :
      env (.rel args) head =
        WireQuantifierSemantics.contentRelation model definitionEnv
          contentCompiled boundaryExact parameterValues)
    (boundaryValues :
      Vars.denote env attachment.positions =
        boundaryExact.symm ▸
          WireQuantifierSemantics.appendArgs
            (Vars.denote env arguments) parameterValues) :
    denoteItem model.toPreModel definitionEnv env (.atom head arguments) ↔
      denoteRegion model.toPreModel definitionEnv env
        (intrinsicSplice contentCompiled.openDiagram attachment) := by
  rw [denote_intrinsicSplice]
  simp only [denoteItem, headValue]
  rw [WireQuantifierSemantics.contentRelation_applies]
  apply iff_of_eq
  apply congrArg
    (denoteOpen model.toPreModel definitionEnv contentCompiled.openDiagram)
  exact boundaryValues.symm

/--
The accepted intrinsic splice is exactly one compiled application once the
formal prefix is fixed and the remaining ordered positions carry the fixed
parameter tuple.
-/
private theorem compiledApplication_denotes_intrinsic
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {content : CheckedOpenDiagram definitions}
    (contentCompiled : OpenCompilation content)
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {attachment : ConcreteSpliceAttachment base site content}
    (compiled : InsertionCompilation contentCompiled attachment)
    {args parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content = args ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (env : Env model.toPreModel compiled.site.frame.visible.sigs)
    (head : Var compiled.site.frame.visible.sigs (.rel args))
    (arguments : Vars compiled.site.frame.visible.sigs args)
    (formalExact :
      formalVariables args
          (boundaryExact ▸ compiled.intrinsicAttachment.positions) =
        arguments)
    (headValue :
      env (.rel args) head =
        WireQuantifierSemantics.contentRelation model definitionEnv
          contentCompiled boundaryExact parameterValues)
    (parameterExact :
      Vars.denote env
          (parameterVariables args
            (boundaryExact ▸ compiled.intrinsicAttachment.positions)) =
        parameterValues) :
    denoteItem model.toPreModel definitionEnv env (.atom head arguments) ↔
      denoteRegion model.toPreModel definitionEnv env
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment) := by
  apply
    application_denotes_intrinsic model definitionEnv contentCompiled
      boundaryExact parameterValues env head arguments
      compiled.intrinsicAttachment headValue
  rw [boundary_values_from_formals env boundaryExact
    compiled.intrinsicAttachment.positions arguments formalExact,
    parameterExact]

/--
Transport the compiler-owned application law back to the raw singleton-erasure
visible context. This is the exact `LocalReplacementAt` payload used by both
scope-geometry branches.
-/
private theorem RelationJoinStep.erasureLocalLaw
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (context : ConcreteElaboration.WireContext step.prior.val)
    (visibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context =
        compiled.site.frame.visible)
    (head : Var context.sigs (.rel step.relationArgs))
    (arguments : Vars context.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val context arguments =
        step.priorArguments)
    (rawEnv :
      Env model.toPreModel
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication context).sigs)
    (headValue :
      transportEnvironment step.base_generated.symm
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context)
          compiled.site.frame.visible visibleExact rawEnv
          (.rel step.relationArgs)
          (baseRenamedVariable step context compiled.site.frame.visible
            visibleExact head) =
        WireQuantifierSemantics.contentRelation model definitionEnv
          contentCompiled boundaryExact parameterValues)
    (parameterExact :
      Vars.denote
          (transportEnvironment step.base_generated.symm
            (SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication context)
            compiled.site.frame.visible visibleExact rawEnv)
          (parameterVariables step.relationArgs
            (boundaryExact ▸ compiled.intrinsicAttachment.positions)) =
        parameterValues) :
    denoteRegion model.toPreModel definitionEnv rawEnv
        (untransportRegion step.base_generated.symm
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication context)
          compiled.site.frame.visible visibleExact
          (intrinsicSplice contentCompiled.openDiagram
            compiled.intrinsicAttachment)) ↔
      denoteItem model.toPreModel definitionEnv
        (Env.comp rawEnv
          (SingletonRemovalSemantics.contextRenaming step.prior
            step.priorApplication context))
        (.atom head arguments) := by
  let baseEnv :=
    transportEnvironment step.base_generated.symm
      (SingletonRemovalSemantics.targetContext step.prior
        step.priorApplication context)
      compiled.site.frame.visible visibleExact rawEnv
  have formalExact :=
    RelationJoinStep.formalVariables_exact step contentCompiled compiled
      boundaryExact context visibleExact arguments argumentOrigins
  have intrinsicLaw :=
    compiledApplication_denotes_intrinsic model definitionEnv contentCompiled
      compiled boundaryExact parameterValues baseEnv
      (baseRenamedVariable step context compiled.site.frame.visible
        visibleExact head)
      (baseRenamedVariables step context compiled.site.frame.visible
        visibleExact arguments)
      formalExact headValue parameterExact
  rw [untransportRegion_denotes]
  constructor
  · intro intrinsicHolds
    have atomHolds := intrinsicLaw.mpr intrinsicHolds
    simpa [baseEnv, denoteItem,
      Internal.RelationJoinStep.baseRenamedVariable,
      Internal.RelationJoinStep.baseRenamedVariables,
      transportEnvironment_apply,
      transportEnvironment_denote, Vars.denote_rename] using atomHolds
  · intro atomHolds
    apply intrinsicLaw.mp
    simpa [baseEnv, denoteItem,
      Internal.RelationJoinStep.baseRenamedVariable,
      Internal.RelationJoinStep.baseRenamedVariables,
      transportEnvironment_apply,
      transportEnvironment_denote, Vars.denote_rename] using atomHolds

/--
Cast the canonical erasure law to the actual compiler-generated target frame.
The replacement remains the transported accepted intrinsic splice.
-/
theorem Internal.RelationJoinStep.erasureLocalReplacementAt
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    {sourceOuter : ConcreteElaboration.WireContext step.prior.val}
    (sourceFrame : RegionFrame definitions step.prior.val sourceOuter)
    {fuel : Nat}
    (targetFrame :
      RegionFrame definitions
        (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
          step.prior step.priorApplication)
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceOuter))
    (provenance :
      SingletonRemovalSemantics.ErasureFrameProvenance step.prior
        step.priorApplication
        (step.priorRegionImage step.sourceRegion) fuel sourceOuter
        (step.priorRegionImage (source.val.wires dying).scope)
        sourceFrame targetFrame)
    (baseVisibleExact :
      step.base_generated.symm ▸
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceFrame.visible =
        compiled.site.frame.visible)
    (head : Var sourceFrame.visible.sigs (.rel step.relationArgs))
    (arguments : Vars sourceFrame.visible.sigs step.relationArgs)
    (argumentOrigins :
      ConcreteElaboration.variableOrigins step.prior.val
          sourceFrame.visible arguments =
        step.priorArguments)
    (targetEnv : Env model.toPreModel targetFrame.visible.sigs)
    (headValue :
      let canonicalEnv :=
        congrArg ConcreteElaboration.WireContext.sigs
            provenance.targetVisible ▸ targetEnv
      transportEnvironment step.base_generated.symm
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceFrame.visible)
          compiled.site.frame.visible baseVisibleExact canonicalEnv
          (.rel step.relationArgs)
          (baseRenamedVariable step sourceFrame.visible
            compiled.site.frame.visible baseVisibleExact head) =
        WireQuantifierSemantics.contentRelation model definitionEnv
          contentCompiled boundaryExact parameterValues)
    (parameterExact :
      let canonicalEnv :=
        congrArg ConcreteElaboration.WireContext.sigs
            provenance.targetVisible ▸ targetEnv
      Vars.denote
          (transportEnvironment step.base_generated.symm
            (SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication sourceFrame.visible)
            compiled.site.frame.visible baseVisibleExact canonicalEnv)
          (parameterVariables step.relationArgs
            (boundaryExact ▸ compiled.intrinsicAttachment.positions)) =
        parameterValues) :
    let canonicalReplacement :=
      untransportRegion step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceFrame.visible)
        compiled.site.frame.visible baseVisibleExact
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment)
    let replacement :=
      congrArg ConcreteElaboration.WireContext.sigs
          provenance.targetVisible.symm ▸ canonicalReplacement
    SingletonRemovalSemantics.LocalReplacementAt step.prior
      step.priorApplication sourceFrame.visible targetFrame.visible
      provenance.targetVisible replacement (.atom head arguments)
      model.toPreModel definitionEnv targetEnv := by
  dsimp only
  apply
    SingletonRemovalSemantics.LocalReplacementAt.cast step.prior
      step.priorApplication rfl provenance.targetVisible.symm rfl
      provenance.targetVisible
      (untransportRegion step.base_generated.symm
        (SingletonRemovalSemantics.targetContext step.prior
          step.priorApplication sourceFrame.visible)
        compiled.site.frame.visible baseVisibleExact
        (intrinsicSplice contentCompiled.openDiagram
          compiled.intrinsicAttachment))
      (.atom head arguments) model.toPreModel definitionEnv targetEnv
  exact
    RelationJoinStep.erasureLocalLaw step contentCompiled compiled model
      definitionEnv boundaryExact parameterValues sourceFrame.visible
      baseVisibleExact head arguments argumentOrigins
      (congrArg ConcreteElaboration.WireContext.sigs
        provenance.targetVisible ▸ targetEnv)
      headValue parameterExact

/--
At a co-scoped application, consume the singleton-erasure receipt without
closing the dying-scope binders. The resulting equivalence is exactly between
the replacement-conjoined erased site body and the original site body.
-/
private theorem RelationJoinStep.coScopedErasureBodyDenotation
    {source : CheckedDiagram definitions}
    {dying : source.val.WireId}
    {content : CheckedOpenDiagram definitions}
    (step : RelationJoinStep source dying content)
    (contentCompiled : OpenCompilation content)
    (compiled : InsertionCompilation contentCompiled step.attachment)
    (model : Model.{u})
    (definitionEnv :
      DefinitionEnv model.toPreModel definitions)
    {parameterSigs : List Sig}
    (boundaryExact :
      checkedBoundarySigs content =
        step.relationArgs ++ parameterSigs)
    (parameterValues :
      PreModel.Args model.toPreModel.Domain parameterSigs)
    (coScoped :
      (source.val.wires dying).scope = step.sourceRegion) :
    ∃ (outer : ConcreteElaboration.WireContext step.prior.val)
      (fuel : Nat)
      (sourceFrame : RegionFrame definitions step.prior.val outer)
      (targetFrame :
        RegionFrame definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication outer))
      (provenance :
        SingletonRemovalSemantics.ErasureFrameProvenance step.prior
          step.priorApplication
          (step.priorRegionImage step.sourceRegion) fuel outer
          (step.priorRegionImage (source.val.wires dying).scope)
          sourceFrame targetFrame)
      (siteOuter : ConcreteElaboration.WireContext step.base.val)
      (generatedFrame :
        RegionFrame definitions step.attachment.diagram
          (InsertionCompilation.NaturalityInternal.hostContext
            step.attachment
            (checkedBaseFrameReceipt step
              (step.priorRegionImage step.sourceRegion)
              (step.priorRegionImage (source.val.wires dying).scope)
              fuel outer targetFrame provenance.targetGenerated).outer))
      (pairedInsertion :
        InsertionCompilation.PairedGeneratedFrame compiled
          (step.baseRegionImage (source.val.wires dying).scope)
          fuel
          (checkedBaseFrameReceipt step
            (step.priorRegionImage step.sourceRegion)
            (step.priorRegionImage (source.val.wires dying).scope)
            fuel outer targetFrame provenance.targetGenerated).outer
          siteOuter
          (checkedBaseFrameReceipt step
            (step.priorRegionImage step.sourceRegion)
            (step.priorRegionImage (source.val.wires dying).scope)
            fuel outer targetFrame provenance.targetGenerated).frame
          generatedFrame)
      (visibleExact :
        targetFrame.visible =
          SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication sourceFrame.visible)
      (baseVisibleExact :
        step.base_generated.symm ▸
            SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication sourceFrame.visible =
          compiled.site.frame.visible)
      (head : Var sourceFrame.visible.sigs (.rel step.relationArgs))
      (arguments : Vars sourceFrame.visible.sigs step.relationArgs)
      (replacement : Region definitions targetFrame.visible.sigs),
      compileRegionFrame? definitions step.prior.val
          (step.priorRegionImage step.sourceRegion) fuel
          (step.priorRegionImage (source.val.wires dying).scope) outer =
        some sourceFrame ∧
      compileRegionFrame? definitions
          (ConcreteDiagram.IdentityNormalizationCore.eraseNodeCandidate
            step.prior step.priorApplication)
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage step.sourceRegion))
          fuel
          (SingletonRemovalSemantics.targetRegion step.prior
            step.priorApplication
            (step.priorRegionImage (source.val.wires dying).scope))
          (SingletonRemovalSemantics.targetContext step.prior
            step.priorApplication outer) =
        some targetFrame ∧
      ∀ targetEnv : Env model.toPreModel targetFrame.visible.sigs,
        (let canonicalEnv :=
          congrArg ConcreteElaboration.WireContext.sigs
              visibleExact ▸ targetEnv
         transportEnvironment step.base_generated.symm
            (SingletonRemovalSemantics.targetContext step.prior
              step.priorApplication sourceFrame.visible)
            compiled.site.frame.visible
            baseVisibleExact
            canonicalEnv (.rel step.relationArgs)
            (baseRenamedVariable step sourceFrame.visible
              compiled.site.frame.visible baseVisibleExact head) =
          WireQuantifierSemantics.contentRelation model definitionEnv
            contentCompiled boundaryExact parameterValues) →
        (let canonicalEnv :=
          congrArg ConcreteElaboration.WireContext.sigs
              visibleExact ▸ targetEnv
         Vars.denote
            (transportEnvironment step.base_generated.symm
              (SingletonRemovalSemantics.targetContext step.prior
                step.priorApplication sourceFrame.visible)
              compiled.site.frame.visible baseVisibleExact canonicalEnv)
            (parameterVariables step.relationArgs
              (boundaryExact ▸ compiled.intrinsicAttachment.positions)) =
          parameterValues) →
        (denoteRegion model.toPreModel definitionEnv targetEnv
              (replacement.conjoin targetFrame.siteBody) ↔
          denoteRegion model.toPreModel definitionEnv
            (Env.comp
              (congrArg ConcreteElaboration.WireContext.sigs
                  visibleExact ▸ targetEnv)
              (SingletonRemovalSemantics.contextRenaming step.prior
                step.priorApplication sourceFrame.visible))
            sourceFrame.siteBody) := by
  obtain ⟨_scopeCompiled, outer, fuel, sourceFrame, sourceVisible,
      _inner, _scopeVisible, _sourceAbove, sourceGenerated,
      _sourceFrameBody, _sourceDecomposition, _scopeBody, pairedErasure⟩ :=
    RelationJoinStep.dyingScopeErasure step
  obtain ⟨head, arguments, applicationCompiled, _headOrigin,
      argumentOrigins⟩ :=
    Internal.RelationJoinStep.relativeCompiledApplication step sourceFrame sourceVisible
  obtain ⟨targetFrame, provenance, siteOuter, generatedFrame,
      pairedInsertion⟩ :=
    RelationJoinStep.pairedInsertionAtDying step contentCompiled compiled
      sourceVisible pairedErasure
  have baseVisibleExact :=
    RelationJoinStep.pairedInsertion_baseVisibleExact step contentCompiled
      compiled targetFrame provenance pairedInsertion
  have pairedFixed :
      SingletonRemovalSemantics.PairedGeneratedFrame step.prior
        step.priorApplication
        (step.prior.val.nodes step.priorApplication).region
        (step.prior.val.nodes step.priorApplication).region fuel outer
        sourceFrame := by
    simpa [step.priorNodeExact, coScoped] using pairedErasure
  obtain ⟨fixedTarget, fixedGenerated, fixedVisible, fixedLaw⟩ :=
    SingletonRemovalSemantics.PairedGeneratedFrame.fixedScope_replacement_denotation
      step.prior step.priorApplication
      (SingletonRemovalSemantics.RelationJoinStep.checkedErasure step)
      fuel outer
      sourceFrame pairedFixed (.atom head arguments) applicationCompiled
      model.toPreModel definitionEnv
  have targetSame : fixedTarget = targetFrame := by
    apply Option.some.inj
    exact fixedGenerated.symm.trans (by
      simpa [step.priorNodeExact, coScoped] using provenance.targetGenerated)
  subst fixedTarget
  let canonicalReplacement :=
    untransportRegion step.base_generated.symm
      (SingletonRemovalSemantics.targetContext step.prior
        step.priorApplication sourceFrame.visible)
      compiled.site.frame.visible baseVisibleExact
      (intrinsicSplice contentCompiled.openDiagram
        compiled.intrinsicAttachment)
  let replacement :=
    congrArg ConcreteElaboration.WireContext.sigs
        provenance.targetVisible.symm ▸ canonicalReplacement
  refine
    ⟨outer, fuel, sourceFrame, targetFrame, provenance, siteOuter,
      generatedFrame, pairedInsertion, provenance.targetVisible,
      baseVisibleExact, head, arguments, replacement, sourceGenerated,
      provenance.targetGenerated, ?_⟩
  intro targetEnv headValue parameterExact
  apply fixedLaw replacement targetEnv
  exact
    Internal.RelationJoinStep.erasureLocalReplacementAt step contentCompiled compiled
      model definitionEnv boundaryExact parameterValues sourceFrame
      targetFrame provenance baseVisibleExact head arguments argumentOrigins
      targetEnv headValue parameterExact


end RelationJoinSemantics

end ConcreteWireQuantifier

end VisualProof
