import VisualProof.Diagram.Concrete.ElaborationInvariance
import VisualProof.Diagram.Concrete.Subgraph.Extract

namespace VisualProof

universe u

namespace Var

/-- Equality of intrinsically typed variables is structurally decidable. -/
def decEq : (left right : Var ctx sig) → Decidable (left = right)
  | .here, .here => isTrue rfl
  | .here, .there _ => isFalse fun equality => by cases equality
  | .there _, .here => isFalse fun equality => by cases equality
  | .there left, .there right =>
      match decEq left right with
      | isTrue equality => isTrue (by cases equality; rfl)
      | isFalse different => isFalse fun equality => by
          cases equality
          exact different rfl

instance : DecidableEq (Var ctx sig) := decEq

end Var

namespace Vars

/--
One source class and one target variable occupy the same ordered boundary
position. This is structural evidence about the supplied attachment tuple.
-/
inductive Paired :
    {args : List Sig} → Vars source args → Vars target args →
      {sig : Sig} → Var source sig → Var target sig → Prop
  | head :
      Paired (.cons source sourceTail) (.cons target targetTail) source target
  | tail :
      Paired sourceTail targetTail source target →
        Paired (.cons otherSource sourceTail) (.cons otherTarget targetTail)
          source target

/-- Equal ordered boundary tuples give equal values at paired positions. -/
theorem value_eq_of_paired
    {sources : Vars source args} {targets : Vars target args}
    {sourceVar : Var source sig} {targetVar : Var target sig}
    (paired : Paired sources targets sourceVar targetVar)
    (left : Env pre source) (right : Env pre target)
    (valuesEqual : Vars.denote left sources = Vars.denote right targets) :
    left sig sourceVar = right sig targetVar := by
  induction paired with
  | head => exact congrArg Prod.fst valuesEqual
  | tail _ induction =>
      exact induction (congrArg Prod.snd valuesEqual)

end Vars

/--
An ordered boundary attachment. `positions` names every external position;
`classMap` chooses one representative target wire for each aliased source
class. Intrinsic typing is the signature check and makes capture impossible.
-/
structure SpliceAttachment (fragment : OpenDiagram defs args)
    (target : List Sig) where
  positions : Vars target args
  classMap : WireRenaming fragment.classes target
  representative_position :
    ∀ {sig} (fiber : Var fragment.classes sig),
      Vars.Paired fragment.boundary positions fiber (classMap fiber)

namespace SpliceAttachment

private def targetsFor :
    {args : List Sig} →
      (fiber : Var source sig) →
      Vars source args → Vars target args → List (Var target sig)
  | [], _, .nil, .nil => []
  | _ :: _, fiber, .cons sourceHead sourceTail,
      .cons targetHead targetTail =>
      if equality :
          (⟨_, sourceHead⟩ : PackedVar source) =
            (⟨_, fiber⟩ : PackedVar source) then
        match equality with
        | rfl => targetHead :: targetsFor sourceHead sourceTail targetTail
      else
        targetsFor fiber sourceTail targetTail

private theorem mem_targetsFor_iff
    (fiber : Var source sig)
    (sources : Vars source args)
    (targets : Vars target args)
    (value : Var target sig) :
    value ∈ targetsFor fiber sources targets ↔
      Vars.Paired sources targets fiber value := by
  induction sources with
  | nil =>
      cases targets
      constructor
      · simp [targetsFor]
      · intro impossible
        nomatch impossible
  | cons sourceHead sourceTail induction =>
      cases targets with
      | cons targetHead targetTail =>
          by_cases equality :
              (⟨_, sourceHead⟩ : PackedVar source) =
                (⟨_, fiber⟩ : PackedVar source)
          · cases equality
            simp only [targetsFor, ↓reduceDIte, List.mem_cons]
            constructor
            · intro member
              rcases member with rfl | tailMember
              · exact .head
              · exact .tail ((induction targetTail).mp tailMember)
            · intro paired
              cases paired with
              | head => exact Or.inl rfl
              | tail tailPaired =>
                  exact Or.inr ((induction targetTail).mpr tailPaired)
          · simp only [targetsFor, equality, ↓reduceDIte]
            constructor
            · intro member
              exact .tail ((induction targetTail).mp member)
            · intro paired
              cases paired with
              | head => exact (equality rfl).elim
              | tail tailPaired =>
                  exact (induction targetTail).mpr tailPaired

private def classEqual
    (sources : Vars source args)
    (targets : Vars target args)
    (env : Env pre target) :
    PackedVar source → Prop
  | ⟨sig, fiber⟩ =>
      AllEqual
        (((targetsFor fiber sources targets).eraseDups).map (env sig))

private theorem allEqual_of_length_lt_two
    (values : List α) (short : values.length < 2) :
    AllEqual values := by
  cases values with
  | nil => simp [AllEqual]
  | cons head tail =>
      cases tail with
      | nil => simp [AllEqual]
      | cons second rest =>
          simp only [List.length_cons] at short
          omega

private def buildClassIdentities
    (sources : Vars source args)
    (targets : Vars target args) :
    List (PackedVar source) → ItemSeq defs target
  | [] => .nil
  | ⟨sig, fiber⟩ :: tail =>
      let ports := (targetsFor fiber sources targets).eraseDups
      if enough : 2 ≤ ports.length then
        .cons (.identity sig ports enough)
          (buildClassIdentities sources targets tail)
      else
        buildClassIdentities sources targets tail

private theorem buildClassIdentities_denote
    (sources : Vars source args)
    (targets : Vars target args)
    (classes : List (PackedVar source))
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (env : Env pre target) :
    denoteItemSeq pre definitionEnv env
        (buildClassIdentities sources targets classes) ↔
      ∀ packed, packed ∈ classes →
        classEqual sources targets env packed := by
  induction classes with
  | nil =>
      simp [buildClassIdentities]
  | cons packed tail induction =>
      rcases packed with ⟨sig, fiber⟩
      let ports := (targetsFor fiber sources targets).eraseDups
      by_cases enough : 2 ≤ ports.length
      · simp only [buildClassIdentities, ports, enough, ↓reduceDIte,
          denoteItemSeq_cons, denoteItem_identity, induction,
          List.mem_cons, forall_eq_or_imp]
        rfl
      · have short : ports.length < 2 := by omega
        have automatic : AllEqual (ports.map (env sig)) := by
          apply allEqual_of_length_lt_two
          simpa only [List.length_map] using short
        simp only [buildClassIdentities, ports, enough, ↓reduceDIte,
          induction, List.mem_cons, forall_eq_or_imp]
        exact Iff.intro
          (fun tailEqual => ⟨automatic, tailEqual⟩)
          (fun both => both.2)

private def buildIdentities
    (sources : Vars source args)
    (targets : Vars target args) :
    ItemSeq defs target :=
  buildClassIdentities sources targets sources.entries.eraseDups

private theorem source_mem_of_paired
    {source target : List Sig}
    {args : List Sig}
    {sig : Sig}
    {sources : Vars source args}
    {targets : Vars target args}
    {sourceValue : Var source sig}
    {targetValue : Var target sig}
    (paired : Vars.Paired sources targets sourceValue targetValue) :
    (⟨_, sourceValue⟩ : PackedVar source) ∈ sources.entries := by
  induction paired with
  | head => simp [Vars.entries]
  | tail _ induction => exact List.mem_cons_of_mem _ induction

private theorem paired_values_equal_of_classes
    (attachment : SpliceAttachment fragment target)
    (pre : PreModel.{u})
    (env : Env pre target)
    (classes :
      ∀ packed, packed ∈ fragment.boundary.entries.eraseDups →
        classEqual fragment.boundary attachment.positions env packed)
    {sig : Sig}
    (fiber : Var fragment.classes sig)
    (value : Var target sig)
    (paired :
      Vars.Paired fragment.boundary attachment.positions fiber value) :
    env sig (attachment.classMap fiber) = env sig value := by
  have classMember :
      (⟨sig, fiber⟩ : PackedVar fragment.classes) ∈
        fragment.boundary.entries.eraseDups := by
    simp only [List.mem_eraseDups]
    exact source_mem_of_paired paired
  have equalClass := classes ⟨sig, fiber⟩ classMember
  have representativeMember :
      attachment.classMap fiber ∈
        targetsFor fiber fragment.boundary attachment.positions :=
    (mem_targetsFor_iff fiber fragment.boundary attachment.positions
      (attachment.classMap fiber)).mpr
      (attachment.representative_position fiber)
  have valueMember :
      value ∈ targetsFor fiber fragment.boundary attachment.positions :=
    (mem_targetsFor_iff fiber fragment.boundary attachment.positions value).mpr
      paired
  apply equalClass
  · exact List.mem_map.mpr
      ⟨attachment.classMap fiber, by simpa using representativeMember, rfl⟩
  · exact List.mem_map.mpr
      ⟨value, by simpa using valueMember, rfl⟩

private theorem denote_eq_of_paired_values
    (sources : Vars source args)
    (targets : Vars target args)
    (left : Env pre source)
    (right : Env pre target)
    (equal :
      ∀ {sig} (sourceValue : Var source sig)
        (targetValue : Var target sig),
        Vars.Paired sources targets sourceValue targetValue →
          left sig sourceValue = right sig targetValue) :
    Vars.denote left sources = Vars.denote right targets := by
  induction sources with
  | nil =>
      cases targets
      rfl
  | cons sourceHead sourceTail induction =>
      cases targets with
      | cons targetHead targetTail =>
          simp only [Vars.denote_cons, PreModel.Args, Prod.mk.injEq]
          constructor
          · exact equal sourceHead targetHead .head
          · apply induction
            intro sig sourceValue targetValue paired
            exact equal sourceValue targetValue (.tail paired)

private theorem classes_of_boundary_denote_eq
    (attachment : SpliceAttachment fragment target)
    (pre : PreModel.{u})
    (env : Env pre target)
    (same :
      Vars.denote (Env.comp env attachment.classMap) fragment.boundary =
        Vars.denote env attachment.positions) :
    ∀ packed, packed ∈ fragment.boundary.entries.eraseDups →
      classEqual fragment.boundary attachment.positions env packed := by
  rintro ⟨sig, fiber⟩ classMember
  intro left leftMember right rightMember
  rcases List.mem_map.mp leftMember with
    ⟨leftVar, leftTargetMember, rfl⟩
  rcases List.mem_map.mp rightMember with
    ⟨rightVar, rightTargetMember, rfl⟩
  have leftPaired :
      Vars.Paired fragment.boundary attachment.positions fiber leftVar :=
    (mem_targetsFor_iff fiber fragment.boundary attachment.positions
      leftVar).mp (by simpa using leftTargetMember)
  have rightPaired :
      Vars.Paired fragment.boundary attachment.positions fiber rightVar :=
    (mem_targetsFor_iff fiber fragment.boundary attachment.positions
      rightVar).mp (by simpa using rightTargetMember)
  exact
    (Vars.value_eq_of_paired leftPaired
      (Env.comp env attachment.classMap) env same).symm.trans
      (Vars.value_eq_of_paired rightPaired
        (Env.comp env attachment.classMap) env same)

/--
Materialize only mismatches between an ordered attachment and its class
representative. Repeated source positions attached to distinct target wires
therefore create an identity; exact aliases create no node. Task 6 alone owns
normalization of the resulting identities.
-/
def identities (attachment : SpliceAttachment fragment target) :
    ItemSeq defs target :=
  buildIdentities fragment.boundary attachment.positions

private theorem identities_denote
    (attachment : SpliceAttachment fragment target)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (env : Env pre target) :
    denoteItemSeq pre definitionEnv env attachment.identities ↔
      Vars.denote (Env.comp env attachment.classMap) fragment.boundary =
        Vars.denote env attachment.positions := by
  rw [identities, buildIdentities, buildClassIdentities_denote]
  constructor
  · intro classes
    apply denote_eq_of_paired_values
    intro sig sourceValue targetValue paired
    exact paired_values_equal_of_classes attachment pre env classes
      sourceValue targetValue paired
  · exact classes_of_boundary_denote_eq attachment pre env

end SpliceAttachment

/--
Capture-avoiding intrinsic splice. The body is renamed into the visible hole
context and explicit boundary identities are conjoined there.
-/
def intrinsicSplice (fragment : OpenDiagram defs args)
    (attachment : SpliceAttachment fragment target) :
    Region defs target :=
  Region.surround attachment.identities
    (fragment.body.renameWires attachment.classMap) .nil

/-- Place a capture-avoiding splice through a genuine one-hole context. -/
def intrinsicSpliceIn (context : DiagramContext defs target outer)
    (fragment : OpenDiagram defs args)
    (attachment : SpliceAttachment fragment target) :
    Region defs outer :=
  context.fill (intrinsicSplice fragment attachment)

/--
Splice denotes exactly the open fragment at the ordered supplied values.
The reverse direction uses boundary surjectivity to identify the existential
class environment with the representative environment; it is not definitional.
-/
theorem denote_intrinsicSplice
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (env : Env pre target) (fragment : OpenDiagram defs args)
    (attachment : SpliceAttachment fragment target) :
    denoteRegion pre definitionEnv env (intrinsicSplice fragment attachment) ↔
      denoteOpen pre definitionEnv fragment
        (Vars.denote env attachment.positions) := by
  rw [intrinsicSplice, Region.denote_surround,
    SpliceAttachment.identities_denote,
    denoteRegion_renameWires]
  simp only [denoteItemSeq_nil, and_true]
  constructor
  · rintro ⟨boundaryEqual, body⟩
    exact ⟨Env.comp env attachment.classMap, boundaryEqual, body⟩
  · rintro ⟨classEnv, boundaryEqual, body⟩
    have environmentsEqual :
        classEnv = Env.comp env attachment.classMap := by
      funext sig fiber
      exact Vars.value_eq_of_paired
        (attachment.representative_position fiber) classEnv env boundaryEqual
    subst classEnv
    exact ⟨boundaryEqual, body⟩

/--
Equivalent open fragments remain equivalent after splice at every context
depth; polarity is discharged by `context_equiv`.
-/
theorem denote_intrinsicSplice_in_context
    (context : DiagramContext defs target outer)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (left : OpenDiagram defs leftArgs)
    (leftAttachment : SpliceAttachment left target)
    (right : OpenDiagram defs rightArgs)
    (rightAttachment : SpliceAttachment right target)
    (equivalent : ∀ env : Env pre target,
      denoteOpen pre definitionEnv left
          (Vars.denote env leftAttachment.positions) ↔
        denoteOpen pre definitionEnv right
          (Vars.denote env rightAttachment.positions))
    (env : Env pre outer) :
    denoteRegion pre definitionEnv env
        (intrinsicSpliceIn context left leftAttachment) ↔
      denoteRegion pre definitionEnv env
        (intrinsicSpliceIn context right rightAttachment) := by
  apply context_equiv context pre definitionEnv
  intro holeEnv
  rw [denote_intrinsicSplice, denote_intrinsicSplice]
  exact equivalent holeEnv

/--
One source boundary class whose distinct positional attachments require one
orderless n-ary identity node. The attachment list retains first-seen boundary
order solely to give the concrete ports deterministic names.
-/
structure ConcreteIdentityRequest
    (base : ConcreteDiagram baseDefinitionCount)
    (fragment : ConcreteDiagram fragmentDefinitionCount) where
  source : fragment.WireId
  attachments : List base.WireId
  deriving DecidableEq

namespace ConcreteIdentityRequest

/-- The identity signature is determined by its source boundary class. -/
def sig
    (request : ConcreteIdentityRequest base fragment) : Sig :=
  (fragment.wires request.source).sig

end ConcreteIdentityRequest

def concreteRepresentativePosition
    (fragment : CheckedOpenDiagram definitions)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ fragment.val.boundary) :
    Fin fragment.val.boundary.length :=
  DenseList.index fragment.val.boundary wire member

def concreteRepresentativeTarget
    (base : CheckedDiagram definitions)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length →
        base.val.WireId)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ fragment.val.boundary) :
    base.val.WireId :=
  target (concreteRepresentativePosition fragment wire member)

/--
The distinct host attachments of one source class, in first-seen boundary
position order.
-/
def concreteAttachmentTargets
    (base : CheckedDiagram definitions)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length →
        base.val.WireId)
    (source : fragment.val.diagram.WireId) :
    List base.val.WireId :=
  ((Data.Finite.allFin fragment.val.boundary.length).filterMap fun position =>
    if fragment.val.boundary.get position = source then
      some (target position)
    else
      none).eraseDups

/--
Canonical grouped identity requests computed from positional targets. There is
at most one request per source boundary class, and it contains every distinct
host attachment for that class. Singleton classes require no identity node.
-/
def computedIdentityRequests
    (base : CheckedDiagram definitions)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length →
        base.val.WireId) :
    List (ConcreteIdentityRequest base.val fragment.val.diagram) :=
  (fragment.val.boundary.eraseDups.filterMap fun source =>
    let attachments :=
      concreteAttachmentTargets base fragment target source
    if 2 ≤ attachments.length then
      some { source := source, attachments := attachments }
    else
      none).eraseDups

/--
Concrete attachments are indexed by genuine generated boundary positions.
Typing and enclosure are explicit, validated data; no target search occurs.
-/
structure ConcreteSpliceAttachment
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId)
    (fragment : CheckedOpenDiagram definitions) where
  private mk ::
  private targetFn :
    Fin fragment.val.boundary.length →
      base.val.WireId
  private signatureProof :
    ∀ position,
      (base.val.wires (targetFn position)).sig =
        (fragment.val.diagram.wires
          (fragment.val.boundary.get position)).sig
  private scopeProof :
    ∀ position,
      base.val.Encloses
        (base.val.wires (targetFn position)).scope
        site

namespace ConcreteSpliceAttachment

/-- The exact supplied positional target function. -/
def target
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Fin fragment.val.boundary.length → base.val.WireId :=
  attachment.targetFn

/-- Every supplied target has the signature of its boundary position. -/
theorem signature
    (attachment : ConcreteSpliceAttachment base site fragment)
    (position : Fin fragment.val.boundary.length) :
    (base.val.wires (attachment.target position)).sig =
      (fragment.val.diagram.wires
        (fragment.val.boundary.get position)).sig :=
  attachment.signatureProof position

/-- Every supplied target is visible from the splice site. -/
theorem scope
    (attachment : ConcreteSpliceAttachment base site fragment)
    (position : Fin fragment.val.boundary.length) :
    base.val.Encloses
      (base.val.wires (attachment.target position)).scope
      site :=
  attachment.scopeProof position

/-- The grouped identity requests derived from the checked positional target. -/
def identityRequests
    (attachment : ConcreteSpliceAttachment base site fragment) :
    List (ConcreteIdentityRequest base.val fragment.val.diagram) :=
  computedIdentityRequests base fragment attachment.target

/-- Canonical grouped requests contain no duplicate source-class requests. -/
theorem identityRequests_nodup
    (attachment : ConcreteSpliceAttachment base site fragment) :
    attachment.identityRequests.Nodup :=
  Data.Finite.eraseDups_nodup _

/-- Grouped requests are exactly the canonical executable computation. -/
theorem identityRequests_exact
    (attachment : ConcreteSpliceAttachment base site fragment) :
    attachment.identityRequests =
      computedIdentityRequests base fragment attachment.target :=
  rfl

/-- Positional attachment targets that agree whenever their boundary source
wire agrees generate no identity requests. -/
theorem identityRequests_eq_nil_of_boundary_coherent
    (attachment : ConcreteSpliceAttachment base site fragment)
    (coherent :
      ∀ left right : Fin fragment.val.boundary.length,
        fragment.val.boundary.get left =
            fragment.val.boundary.get right →
          attachment.target left = attachment.target right) :
    attachment.identityRequests = [] := by
  rw [attachment.identityRequests_exact]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro request member
  unfold computedIdentityRequests at member
  rw [List.mem_eraseDups, List.mem_filterMap] at member
  rcases member with ⟨source, _, emitted⟩
  let targets :=
    concreteAttachmentTargets base fragment attachment.target source
  have targetsSubsingleton :
      ∀ left ∈ targets, ∀ right ∈ targets, left = right := by
    intro left leftMember right rightMember
    unfold targets concreteAttachmentTargets at leftMember rightMember
    rw [List.mem_eraseDups, List.mem_filterMap] at leftMember rightMember
    rcases leftMember with ⟨leftPosition, _, leftEmission⟩
    rcases rightMember with ⟨rightPosition, _, rightEmission⟩
    split at leftEmission
    · rename_i leftSource
      split at rightEmission
      · rename_i rightSource
        have leftTarget : attachment.target leftPosition = left :=
          Option.some.inj leftEmission
        have rightTarget : attachment.target rightPosition = right :=
          Option.some.inj rightEmission
        rw [← leftTarget, ← rightTarget]
        exact coherent leftPosition rightPosition
          (leftSource.trans rightSource.symm)
      · contradiction
    · contradiction
  have targetsNodup : targets.Nodup := by
    unfold targets concreteAttachmentTargets
    exact Data.Finite.eraseDups_nodup _
  have targetsLength : targets.length ≤ 1 := by
    cases targetsEq : targets with
    | nil => simp
    | cons head tail =>
        cases tailEq : tail with
        | nil => simp
        | cons next rest =>
            rw [targetsEq, tailEq] at targetsNodup targetsSubsingleton
            have different : head ≠ next := by
              rw [List.nodup_cons] at targetsNodup
              exact fun same => targetsNodup.1 (by
                rw [same]
                exact List.mem_cons_self)
            exact False.elim
              (different
                (targetsSubsingleton head List.mem_cons_self next
                  (List.mem_cons_of_mem _ List.mem_cons_self)))
  change
    (if 2 ≤ targets.length then
      some { source := source, attachments := targets }
    else none) = some request at emitted
  split at emitted
  · omega
  · contradiction

end ConcreteSpliceAttachment

/-- Executably validate explicit target positions into a typed attachment. -/
def checkConcreteSpliceAttachment
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length →
        base.val.WireId) :
    Option (ConcreteSpliceAttachment base site fragment) :=
  if signature :
      ∀ position,
        (base.val.wires (target position)).sig =
          (fragment.val.diagram.wires
            (fragment.val.boundary.get position)).sig then
    if scope :
        ∀ position,
          base.val.Encloses
            (base.val.wires (target position)).scope
            site then
      some (ConcreteSpliceAttachment.mk target signature scope)
    else
      none
  else
    none

theorem checkConcreteSpliceAttachment_target
    {definitions : List (List Sig)}
    (base : CheckedDiagram definitions)
    (site : base.val.RegionId)
    (fragment : CheckedOpenDiagram definitions)
    (target :
      Fin fragment.val.boundary.length →
        base.val.WireId)
    (attachment : ConcreteSpliceAttachment base site fragment)
    (accepted :
      checkConcreteSpliceAttachment base site fragment target =
        some attachment) :
    attachment.target = target := by
  simp only [checkConcreteSpliceAttachment] at accepted
  split at accepted
  · split at accepted
    · have same := Option.some.inj accepted
      cases same
      rfl
    · contradiction
  · contradiction

namespace ConcreteSpliceAttachment

/-- The first actual boundary position of a source class. -/
def representativePosition
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ fragment.val.boundary) :
    Fin fragment.val.boundary.length :=
  DenseList.index fragment.val.boundary wire member

/-- Every source class chooses a representative from its supplied positions. -/
def representativeTarget
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : fragment.val.diagram.WireId)
    (member : wire ∈ fragment.val.boundary) :
    base.val.WireId :=
  attachment.target (attachment.representativePosition wire member)

theorem identityRequests_mem_iff
    (attachment : ConcreteSpliceAttachment base site fragment)
    (request : ConcreteIdentityRequest base.val fragment.val.diagram) :
    request ∈ attachment.identityRequests ↔
      request ∈ computedIdentityRequests base fragment attachment.target := by
  rw [attachment.identityRequests_exact]

def fragmentRegions
    (attachment : ConcreteSpliceAttachment base site fragment) :
    List fragment.val.diagram.RegionId :=
  fragment.val.diagram.regionsList.filter fun region =>
    decide (region ≠ fragment.val.diagram.root)

def fragmentInternalWires
    (attachment : ConcreteSpliceAttachment base site fragment) :
    List fragment.val.diagram.WireId :=
  fragment.val.diagram.wiresList.filter fun wire =>
    decide (wire ∉ fragment.val.boundary)

abbrev regionCount
    (attachment : ConcreteSpliceAttachment base site fragment) : Nat :=
  base.val.regionCount + attachment.fragmentRegions.length

abbrev nodeCount
    (attachment : ConcreteSpliceAttachment base site fragment) : Nat :=
  base.val.nodeCount +
    (fragment.val.diagram.nodeCount + attachment.identityRequests.length)

abbrev wireCount
    (attachment : ConcreteSpliceAttachment base site fragment) : Nat :=
  base.val.wireCount + attachment.fragmentInternalWires.length

def hostRegion
    (attachment : ConcreteSpliceAttachment base site fragment)
    (region : base.val.RegionId) :
    Fin attachment.regionCount :=
  Fin.castAdd attachment.fragmentRegions.length region

def freshRegion
    (attachment : ConcreteSpliceAttachment base site fragment)
    (region : Fin attachment.fragmentRegions.length) :
    Fin attachment.regionCount :=
  Fin.natAdd base.val.regionCount region

theorem hostRegion_ne_freshRegion
    (attachment : ConcreteSpliceAttachment base site fragment)
    (hostId : base.val.RegionId)
    (freshId : Fin attachment.fragmentRegions.length) :
    attachment.hostRegion hostId ≠ attachment.freshRegion freshId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [hostRegion, freshRegion] at values
  have bound := hostId.isLt
  omega

/-- The fragment root is identified with the site; all other regions are fresh. -/
def fragmentRegion
    (attachment : ConcreteSpliceAttachment base site fragment)
    (region : fragment.val.diagram.RegionId) :
    Fin attachment.regionCount :=
  if root : region = fragment.val.diagram.root then
    attachment.hostRegion site
  else
    attachment.freshRegion
      (DenseList.index attachment.fragmentRegions region (by
        simp [fragmentRegions, ConcreteDiagram.regionsList,
          Data.Finite.mem_allFin, root]))

def hostNode
    (attachment : ConcreteSpliceAttachment base site fragment)
    (node : base.val.NodeId) :
    Fin attachment.nodeCount :=
  Fin.castAdd
    (fragment.val.diagram.nodeCount + attachment.identityRequests.length)
    node

def fragmentNode
    (attachment : ConcreteSpliceAttachment base site fragment)
    (node : fragment.val.diagram.NodeId) :
    Fin attachment.nodeCount :=
  ⟨base.val.nodeCount + node.val, by
    have bound := node.isLt
    simp only [nodeCount]
    omega⟩

def identityNode
    (attachment : ConcreteSpliceAttachment base site fragment)
    (node : Fin attachment.identityRequests.length) :
    Fin attachment.nodeCount :=
  ⟨base.val.nodeCount + fragment.val.diagram.nodeCount + node.val, by
    have bound := node.isLt
    simp only [nodeCount]
    omega⟩

theorem hostNode_ne_fragmentNode
    (attachment : ConcreteSpliceAttachment base site fragment)
    (hostId : base.val.NodeId)
    (fragmentId : fragment.val.diagram.NodeId) :
    attachment.hostNode hostId ≠ attachment.fragmentNode fragmentId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [hostNode, fragmentNode] at values
  have bound := hostId.isLt
  omega

theorem hostNode_ne_identityNode
    (attachment : ConcreteSpliceAttachment base site fragment)
    (hostId : base.val.NodeId)
    (identityId : Fin attachment.identityRequests.length) :
    attachment.hostNode hostId ≠ attachment.identityNode identityId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [hostNode, identityNode] at values
  have bound := hostId.isLt
  omega

theorem fragmentNode_ne_identityNode
    (attachment : ConcreteSpliceAttachment base site fragment)
    (fragmentId : fragment.val.diagram.NodeId)
    (identityId : Fin attachment.identityRequests.length) :
    attachment.fragmentNode fragmentId ≠
      attachment.identityNode identityId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [fragmentNode, identityNode] at values
  have bound := fragmentId.isLt
  omega

def hostWire
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : base.val.WireId) :
    Fin attachment.wireCount :=
  Fin.castAdd attachment.fragmentInternalWires.length wire

def freshWire
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : Fin attachment.fragmentInternalWires.length) :
    Fin attachment.wireCount :=
  Fin.natAdd base.val.wireCount wire

theorem hostWire_injective
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Function.Injective attachment.hostWire := by
  intro left right same
  apply Fin.ext
  simpa [hostWire] using congrArg Fin.val same

theorem hostWire_ne_freshWire
    (attachment : ConcreteSpliceAttachment base site fragment)
    (hostId : base.val.WireId)
    (freshId : Fin attachment.fragmentInternalWires.length) :
    attachment.hostWire hostId ≠ attachment.freshWire freshId := by
  intro equality
  have values := congrArg Fin.val equality
  simp [hostWire, freshWire] at values
  have bound := hostId.isLt
  omega

/--
Boundary classes reconnect to their representative actual target. Every
nonboundary fragment wire receives a disjoint fresh identifier.
-/
def fragmentWire
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : fragment.val.diagram.WireId) :
    Fin attachment.wireCount :=
  if boundary : wire ∈ fragment.val.boundary then
    attachment.hostWire (attachment.representativeTarget wire boundary)
  else
    attachment.freshWire
      (DenseList.index attachment.fragmentInternalWires wire (by
        simp [fragmentInternalWires, ConcreteDiagram.wiresList,
          Data.Finite.mem_allFin, boundary]))

/-- Rename one retained host endpoint into the enlarged node carrier. -/
def hostEndpoint
    (attachment : ConcreteSpliceAttachment base site fragment)
    (endpoint : CEndpoint base.val.nodeCount) :
    CEndpoint attachment.nodeCount :=
  ⟨attachment.hostNode endpoint.node, endpoint.port⟩

/-- Rename one copied fragment endpoint into its disjoint fresh node carrier. -/
def fragmentEndpoint
    (attachment : ConcreteSpliceAttachment base site fragment)
    (endpoint : CEndpoint fragment.val.diagram.nodeCount) :
    CEndpoint attachment.nodeCount :=
  ⟨attachment.fragmentNode endpoint.node, endpoint.port⟩

def regionTable
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Fin attachment.regionCount → CRegion attachment.regionCount :=
  Fin.addCases
    (fun region =>
      match base.val.regions region with
      | .sheet => .sheet
      | .cut parent => .cut (attachment.hostRegion parent))
    (fun fresh =>
      let source := attachment.fragmentRegions.get fresh
      match fragment.val.diagram.regions source with
      | .sheet => .sheet
      | .cut parent => .cut (attachment.fragmentRegion parent))

def renameHostNode
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (node : base.val.NodeId) :
    CNode attachment.regionCount definitions.length :=
  match base.val.nodes node with
  | .atom region args => .atom (attachment.hostRegion region) args
  | .ref region definition args =>
      .ref (attachment.hostRegion region) definition args
  | .identity region sig arity =>
      .identity (attachment.hostRegion region) sig arity

def renameFragmentNode
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment)
    (node : fragment.val.diagram.NodeId) :
    CNode attachment.regionCount definitions.length :=
  match fragment.val.diagram.nodes node with
  | .atom region args => .atom (attachment.fragmentRegion region) args
  | .ref region definition args =>
      .ref (attachment.fragmentRegion region) definition args
  | .identity region sig arity =>
      .identity (attachment.fragmentRegion region) sig arity

def nodeTable
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Fin attachment.nodeCount →
      CNode attachment.regionCount definitions.length :=
  Fin.addCases
    (fun node => renameHostNode attachment node)
    (Fin.addCases
      (fun node => renameFragmentNode attachment node)
      (fun identity =>
        let request := attachment.identityRequests.get identity
        .identity (attachment.hostRegion site) request.sig
          request.attachments.length))

/-- Every copied fragment incidence, keyed by its mapped destination wire. -/
def fragmentEndpointOccurrences
    (attachment : ConcreteSpliceAttachment base site fragment) :
    List (Fin attachment.wireCount × CEndpoint attachment.nodeCount) :=
  fragment.val.diagram.endpointOccurrences.map fun occurrence =>
    (attachment.fragmentWire occurrence.1,
      attachment.fragmentEndpoint occurrence.2)

/--
Every distinct attachment of a grouped source class occupies one port of its
single n-ary identity node.
-/
def identityEndpointOccurrences
    (attachment : ConcreteSpliceAttachment base site fragment) :
    List (Fin attachment.wireCount × CEndpoint attachment.nodeCount) :=
  (Data.Finite.allFin attachment.identityRequests.length).flatMap fun index =>
    let request := attachment.identityRequests.get index
    let node := attachment.identityNode index
    (Data.Finite.allFin request.attachments.length).map fun port =>
      (attachment.hostWire (request.attachments.get port),
        ⟨node, .identity port.val⟩)

def generatedEndpoints
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : Fin attachment.wireCount) :
    List (CEndpoint attachment.nodeCount) :=
  (attachment.fragmentEndpointOccurrences ++
      attachment.identityEndpointOccurrences).filterMap fun occurrence =>
    if occurrence.1 = wire then some occurrence.2 else none

theorem fragmentEndpoint_mem_generated
    (attachment : ConcreteSpliceAttachment base site fragment)
    (_empty : attachment.identityRequests = [])
    (source : fragment.val.diagram.WireId)
    (endpoint : CEndpoint fragment.val.diagram.nodeCount)
    (incident :
      endpoint ∈ (fragment.val.diagram.wires source).endpoints) :
    attachment.fragmentEndpoint endpoint ∈
      attachment.generatedEndpoints (attachment.fragmentWire source) := by
  apply List.mem_filterMap.mpr
  refine
    ⟨(attachment.fragmentWire source,
        attachment.fragmentEndpoint endpoint), ?_, ?_⟩
  · apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨(source, endpoint), ?_, rfl⟩
    simp [ConcreteDiagram.endpointOccurrences,
      ConcreteDiagram.wiresList, Data.Finite.mem_allFin, incident]
  · simp

theorem generatedEndpoint_origin
    (attachment : ConcreteSpliceAttachment base site fragment)
    (empty : attachment.identityRequests = [])
    (wire : Fin attachment.wireCount)
    (endpoint : CEndpoint attachment.nodeCount)
    (member : endpoint ∈ attachment.generatedEndpoints wire) :
    ∃ source : fragment.val.diagram.WireId,
      ∃ sourceEndpoint : CEndpoint fragment.val.diagram.nodeCount,
        sourceEndpoint ∈
            (fragment.val.diagram.wires source).endpoints ∧
          attachment.fragmentWire source = wire ∧
          attachment.fragmentEndpoint sourceEndpoint = endpoint := by
  unfold generatedEndpoints at member
  rcases List.mem_filterMap.mp member with
    ⟨mappedOccurrence, occurrenceMember, filtered⟩
  have identityLength : attachment.identityRequests.length = 0 := by
    simpa using congrArg List.length empty
  have identityOccurrencesEmpty :
      attachment.identityEndpointOccurrences = [] := by
    have noIdentityIndices :
        Data.Finite.allFin attachment.identityRequests.length = [] := by
      rw [identityLength]
      rfl
    unfold identityEndpointOccurrences
    rw [noIdentityIndices]
    rfl
  have fragmentMember :
      mappedOccurrence ∈ attachment.fragmentEndpointOccurrences := by
    simpa [identityOccurrencesEmpty] using occurrenceMember
  unfold fragmentEndpointOccurrences at fragmentMember
  rcases List.mem_map.mp fragmentMember with
    ⟨sourceOccurrence, sourceMember, mappedEquality⟩
  rcases sourceOccurrence with ⟨source, sourceEndpoint⟩
  have incident :
      sourceEndpoint ∈
        (fragment.val.diagram.wires source).endpoints := by
    simpa [ConcreteDiagram.endpointOccurrences,
      ConcreteDiagram.wiresList, Data.Finite.mem_allFin] using sourceMember
  subst mappedOccurrence
  change
    (if attachment.fragmentWire source = wire then
        some (attachment.fragmentEndpoint sourceEndpoint)
      else none) = some endpoint at filtered
  split at filtered
  · rename_i mappedWire
    exact
      ⟨source, sourceEndpoint, incident, mappedWire,
        Option.some.inj filtered⟩
  · contradiction

def wireTable
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Fin attachment.wireCount →
      CWire attachment.regionCount attachment.nodeCount :=
  Fin.addCases
    (fun wire =>
      let source := base.val.wires wire
      { sig := source.sig
        scope := attachment.hostRegion source.scope
        endpoints :=
          source.endpoints.map attachment.hostEndpoint ++
            attachment.generatedEndpoints (attachment.hostWire wire) })
    (fun fresh =>
      let sourceId := attachment.fragmentInternalWires.get fresh
      let source := fragment.val.diagram.wires sourceId
      { sig := source.sig
        scope := attachment.fragmentRegion source.scope
        endpoints :=
          attachment.generatedEndpoints
            (Fin.natAdd base.val.wireCount fresh) })

/--
The concrete splice candidate copies every base and fragment table,
reconnects boundary classes to actual targets, and materializes requested
identities. No normalization is performed.
-/
def diagram
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (attachment : ConcreteSpliceAttachment base site fragment) :
    ConcreteDiagram definitions.length where
  regionCount := attachment.regionCount
  nodeCount := attachment.nodeCount
  wireCount := attachment.wireCount
  root := attachment.hostRegion base.val.root
  regions := regionTable attachment
  nodes := nodeTable attachment
  wires := wireTable attachment

@[simp] theorem diagram_wire_hostWire
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : base.val.WireId) :
    (attachment.diagram.wires (attachment.hostWire wire)).sig =
      (base.val.wires wire).sig := by
  unfold diagram wireTable hostWire
  simp only [Fin.addCases_left]

@[simp] theorem diagram_wire_hostWire_scope
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : base.val.WireId) :
    (attachment.diagram.wires (attachment.hostWire wire)).scope =
      attachment.hostRegion (base.val.wires wire).scope := by
  unfold diagram wireTable hostWire
  simp only [Fin.addCases_left]

@[simp] theorem diagram_wire_freshWire
    (attachment : ConcreteSpliceAttachment base site fragment)
    (fresh : Fin attachment.fragmentInternalWires.length) :
    (attachment.diagram.wires (attachment.freshWire fresh)).sig =
      (fragment.val.diagram.wires
        (attachment.fragmentInternalWires.get fresh)).sig := by
  unfold diagram wireTable freshWire
  simp only [Fin.addCases_right]

@[simp] theorem diagram_wire_freshWire_scope
    (attachment : ConcreteSpliceAttachment base site fragment)
    (fresh : Fin attachment.fragmentInternalWires.length) :
    (attachment.diagram.wires (attachment.freshWire fresh)).scope =
      attachment.fragmentRegion
        (fragment.val.diagram.wires
          (attachment.fragmentInternalWires.get fresh)).scope := by
  unfold diagram wireTable freshWire
  simp only [Fin.addCases_right]

theorem diagram_wire_fragmentWire_signature_of_internal
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : fragment.val.diagram.WireId)
    (internal : wire ∉ fragment.val.boundary) :
    (attachment.diagram.wires (attachment.fragmentWire wire)).sig =
      (fragment.val.diagram.wires wire).sig := by
  let fresh := DenseList.index attachment.fragmentInternalWires wire (by
    simp [fragmentInternalWires, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, internal])
  have wireExact : attachment.fragmentInternalWires.get fresh = wire :=
    DenseList.get_index _ _ _
  rw [fragmentWire, dif_neg internal]
  rw [attachment.diagram_wire_freshWire, wireExact]

theorem diagram_wire_fragmentWire_scope_of_internal
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : fragment.val.diagram.WireId)
    (internal : wire ∉ fragment.val.boundary) :
    (attachment.diagram.wires (attachment.fragmentWire wire)).scope =
      attachment.fragmentRegion (fragment.val.diagram.wires wire).scope := by
  let fresh := DenseList.index attachment.fragmentInternalWires wire (by
    simp [fragmentInternalWires, ConcreteDiagram.wiresList,
      Data.Finite.mem_allFin, internal])
  have wireExact : attachment.fragmentInternalWires.get fresh = wire :=
    DenseList.get_index _ _ _
  rw [fragmentWire, dif_neg internal]
  rw [attachment.diagram_wire_freshWire_scope, wireExact]

/-- A retained host incidence remains incident after the splice. -/
theorem hostEndpoint_mem_diagram
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : base.val.WireId)
    (endpoint : CEndpoint base.val.nodeCount)
    (incident : endpoint ∈ (base.val.wires wire).endpoints) :
    attachment.hostEndpoint endpoint ∈
      (attachment.diagram.wires (attachment.hostWire wire)).endpoints := by
  unfold diagram wireTable hostWire
  simp only [Fin.addCases_left]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨endpoint, incident, rfl⟩)

/-- A copied fragment incidence is incident to its attached or fresh splice
wire. -/
theorem fragmentEndpoint_mem_diagram
    (attachment : ConcreteSpliceAttachment base site fragment)
    (wire : fragment.val.diagram.WireId)
    (endpoint : CEndpoint fragment.val.diagram.nodeCount)
    (incident : endpoint ∈ (fragment.val.diagram.wires wire).endpoints) :
    attachment.fragmentEndpoint endpoint ∈
      (attachment.diagram.wires
        (attachment.fragmentWire wire)).endpoints := by
  have generated :
      attachment.fragmentEndpoint endpoint ∈
        attachment.generatedEndpoints (attachment.fragmentWire wire) := by
    apply List.mem_filterMap.mpr
    refine ⟨(attachment.fragmentWire wire,
      attachment.fragmentEndpoint endpoint), ?_, by simp⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨(wire, endpoint), ?_, rfl⟩
    simp [ConcreteDiagram.endpointOccurrences,
      ConcreteDiagram.wiresList, Data.Finite.mem_allFin, incident]
  by_cases boundary : wire ∈ fragment.val.boundary
  · rw [show attachment.fragmentWire wire =
        attachment.hostWire
          (attachment.representativeTarget wire boundary) by
      simp [fragmentWire, boundary]] at generated ⊢
    unfold diagram wireTable hostWire
    simp only [Fin.addCases_left]
    exact List.mem_append_right _ generated
  · rw [show attachment.fragmentWire wire =
        attachment.freshWire
          (DenseList.index attachment.fragmentInternalWires wire (by
            simp [fragmentInternalWires, ConcreteDiagram.wiresList,
              Data.Finite.mem_allFin, boundary])) by
      simp [fragmentWire, boundary]] at generated ⊢
    unfold diagram wireTable freshWire
    simp only [Fin.addCases_right]
    exact generated

@[simp] theorem diagram_node_hostNode
    (attachment : ConcreteSpliceAttachment base site fragment)
    (node : base.val.NodeId) :
    attachment.diagram.nodes (attachment.hostNode node) =
      renameHostNode attachment node := by
  unfold diagram nodeTable hostNode
  simp only [Fin.addCases_left]

@[simp] theorem diagram_node_fragmentNode
    (attachment : ConcreteSpliceAttachment base site fragment)
    (node : fragment.val.diagram.NodeId) :
    attachment.diagram.nodes (attachment.fragmentNode node) =
      renameFragmentNode attachment node := by
  have allocated :
      attachment.fragmentNode node =
        Fin.natAdd base.val.nodeCount
          (Fin.castAdd attachment.identityRequests.length node) :=
    Fin.ext (by simp [fragmentNode])
  unfold diagram
  rw [allocated]
  unfold nodeTable
  simp only [Fin.addCases_right, Fin.addCases_left]

@[simp] theorem diagram_node_hostNode_region
    (attachment : ConcreteSpliceAttachment base site fragment)
    (node : base.val.NodeId) :
  (attachment.diagram.nodes (attachment.hostNode node)).region =
      attachment.hostRegion (base.val.nodes node).region := by
  rw [diagram_node_hostNode]
  cases data : base.val.nodes node <;>
    simp [renameHostNode, CNode.region, data]

@[simp] theorem diagram_node_fragmentNode_region
    (attachment : ConcreteSpliceAttachment base site fragment)
    (node : fragment.val.diagram.NodeId) :
  (attachment.diagram.nodes (attachment.fragmentNode node)).region =
      attachment.fragmentRegion (fragment.val.diagram.nodes node).region := by
  rw [diagram_node_fragmentNode]
  cases data : fragment.val.diagram.nodes node <;>
    simp [renameFragmentNode, CNode.region, data]

@[simp] theorem diagram_node_identityNode
    (attachment : ConcreteSpliceAttachment base site fragment)
    (identity : Fin attachment.identityRequests.length) :
    attachment.diagram.nodes (attachment.identityNode identity) =
      .identity (attachment.hostRegion site)
        (attachment.identityRequests.get identity).sig
        (attachment.identityRequests.get identity).attachments.length := by
  have allocated :
      attachment.identityNode identity =
        Fin.natAdd base.val.nodeCount
          (Fin.natAdd fragment.val.diagram.nodeCount identity) :=
    Fin.ext (by simp [identityNode]; omega)
  unfold diagram
  rw [allocated]
  unfold nodeTable
  simp only [Fin.addCases_right]

@[simp] theorem diagram_region_hostRegion
    (attachment : ConcreteSpliceAttachment base site fragment)
    (region : base.val.RegionId) :
    attachment.diagram.regions (attachment.hostRegion region) =
      mapRegion attachment.hostRegion
        (base.val.regions region) := by
  unfold diagram regionTable hostRegion
  simp only [Fin.addCases_left]
  cases data : base.val.regions region <;>
    simp [mapRegion, data]

theorem hostRegion_injective
    (attachment : ConcreteSpliceAttachment base site fragment) :
    Function.Injective attachment.hostRegion := by
  intro left right same
  apply Fin.ext
  simpa [hostRegion] using congrArg Fin.val same

theorem hostRegion_climb
    (attachment : ConcreteSpliceAttachment base site fragment) :
    ∀ (steps : Nat) (region : base.val.RegionId),
      attachment.diagram.climb steps (attachment.hostRegion region) =
        (base.val.climb steps region).map attachment.hostRegion
  | 0, _ => rfl
  | steps + 1, region => by
      cases data : base.val.regions region with
      | sheet =>
          simp only [ConcreteDiagram.climb, diagram_region_hostRegion,
            mapRegion, data]
          rfl
      | cut parent =>
          simp [ConcreteDiagram.climb, diagram_region_hostRegion,
            mapRegion, data, hostRegion_climb attachment steps parent]

theorem hostRegion_encloses_iff
    (attachment : ConcreteSpliceAttachment base site fragment)
    (outer inner : base.val.RegionId) :
    attachment.diagram.Encloses
        (attachment.hostRegion outer) (attachment.hostRegion inner) ↔
      base.val.Encloses outer inner := by
  rw [ConcreteElaboration.encloses_iff_exists,
    ConcreteElaboration.encloses_iff_exists]
  constructor
  · rintro ⟨steps, climbed⟩
    have mapped := climbed
    rw [hostRegion_climb attachment] at mapped
    cases source : base.val.climb steps.val inner with
    | none => simp [source] at mapped
    | some region =>
        rw [source] at mapped
        have same :=
          hostRegion_injective attachment (Option.some.inj mapped)
        subst region
        have bounded :=
          ConcreteElaboration.successfulClimb_le_count _
            base.val base.property steps.val inner outer source
        exact ⟨⟨steps.val, by omega⟩, source⟩
  · rintro ⟨steps, climbed⟩
    let targetSteps : Fin (attachment.diagram.regionCount + 1) :=
      ⟨steps.val, by
        change steps.val < attachment.regionCount + 1
        simp only [ConcreteSpliceAttachment.regionCount]
        omega⟩
    refine ⟨targetSteps, ?_⟩
    rw [hostRegion_climb attachment, climbed]
    rfl

@[simp] theorem diagram_region_freshRegion
    (attachment : ConcreteSpliceAttachment base site fragment)
    (fresh : Fin attachment.fragmentRegions.length) :
    attachment.diagram.regions (attachment.freshRegion fresh) =
      mapRegion attachment.fragmentRegion
        (fragment.val.diagram.regions
          (attachment.fragmentRegions.get fresh)) := by
  unfold diagram regionTable freshRegion
  simp only [Fin.addCases_right]
  cases data :
      fragment.val.diagram.regions
        (attachment.fragmentRegions.get fresh) <;>
    simp [mapRegion, data]

end ConcreteSpliceAttachment

/--
Occurrence reconstruction is the sole thin specialization of generic splice.
It preserves the authoritative ordered pattern boundary, maps every position
through the exact occurrence, and refuses if any attachment wire is absent
from the checked complement.  It is independent of selection extraction:
generic exact occurrences may retain repeated boundary aliases.
-/
def reconstructionAttachment?
    {definitions : List (List Sig)}
    {pattern : CheckedOpenDiagram definitions}
    {host : CheckedDiagram definitions}
    (occurrence : Occurrence pattern host)
    (removed : RemovalResult occurrence) :
    Option (ConcreteSpliceAttachment
      removed.complement removed.site pattern) := by
  let attachments : List host.val.WireId :=
    occurrence.boundaryAttachments
  if retained :
      ∀ position : Fin attachments.length,
        attachments.get position ∈ Removal.wires occurrence then
    exact checkConcreteSpliceAttachment
      removed.complement removed.site pattern
      fun position =>
        Removal.wireIndex occurrence
          (attachments.get
            ⟨position.val, by
              simpa [attachments] using position.isLt⟩)
          (retained
            ⟨position.val, by
              simpa [attachments] using position.isLt⟩)
  else
    exact none

end VisualProof
