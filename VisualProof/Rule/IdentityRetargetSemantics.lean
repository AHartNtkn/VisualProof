import VisualProof.Diagram.Concrete.Subgraph.FactorizationSemantics
import VisualProof.Rule.Identity

namespace VisualProof

namespace IdentityRetargetProof

universe u

def contextLiftOuter :
    {holeCtx outerCtx : List Sig} →
      DiagramContext definitions holeCtx outerCtx →
      WireRenaming outerCtx holeCtx
  | _, _, .hole => fun value => value
  | _, _, .surround _ inner _ => contextLiftOuter inner
  | _, _, .cut inner => contextLiftOuter inner
  | _, _, .bind _ inner =>
      fun value => contextLiftOuter inner (.there value)

/--
An equality available outside a one-hole context guards an equivalence at its
hole through every intervening binder, cut, and conjunction.
-/
private theorem context_equiv_of_outer_eq
    (context : DiagramContext definitions holeCtx outerCtx)
    (source target : Var outerCtx sig)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (left right : Region definitions holeCtx)
    (equivalent :
      ∀ holeEnv : Env pre holeCtx,
        holeEnv sig (contextLiftOuter context source) =
            holeEnv sig (contextLiftOuter context target) →
          (denoteRegion pre definitionEnv holeEnv left ↔
            denoteRegion pre definitionEnv holeEnv right))
    (outerEnv : Env pre outerCtx)
    (equal : outerEnv sig source = outerEnv sig target) :
    denoteRegion pre definitionEnv outerEnv (context.fill left) ↔
      denoteRegion pre definitionEnv outerEnv (context.fill right) := by
  induction context with
  | hole => exact equivalent outerEnv equal
  | surround leading inner suffix induction =>
      rw [DiagramContext.fill, DiagramContext.fill,
        Region.denote_surround, Region.denote_surround]
      exact and_congr Iff.rfl
        (and_congr
          (induction (source := source) (target := target)
            (left := left) (right := right)
            equivalent outerEnv equal)
          Iff.rfl)
  | cut inner induction =>
      simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
        denoteItem, and_true]
      exact not_congr
        (induction (source := source) (target := target)
          (left := left) (right := right)
          equivalent outerEnv equal)
  | bind bound inner induction =>
      simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
        denoteItem, and_true]
      apply exists_congr
      intro value
      apply induction (source := .there source) (target := .there target)
        (left := left) (right := right)
      · exact equivalent
      · exact equal

/--
The compiled identity item equates the values of any two incident concrete
wires resolved in its checked lexical context.
-/
theorem compiled_identity_incident_values_equal
    {definitions : List (List Sig)}
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    {region : diagram.RegionId}
    {sig : Sig}
    {arity : Nat}
    (nodeData : diagram.nodes node = .identity region sig arity)
    (source target : diagram.WireId)
    (sourceIncident : source ∈ diagram.identityIncidentWires node)
    (targetIncident : target ∈ diagram.identityIncidentWires node)
    {items : ItemSeq definitions context.sigs}
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context [node] =
        some items)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre context.sigs)
    (itemsDenote : denoteItemSeq pre definitionEnv env items) :
    ∃ (sourceVar targetVar : Var context.sigs sig),
      ConcreteElaboration.WireContext.origin diagram context.ids sourceVar =
          source ∧
        ConcreteElaboration.WireContext.origin diagram context.ids targetVar =
          target ∧
        env sig sourceVar = env sig targetVar := by
  obtain ⟨ports, two, itemsEquality, origins⟩ :=
    ConcreteElaboration.compileNodes?_identity_origins diagram wellFormed
      context node nodeData compiled
  obtain ⟨sourceVar, sourceMember, sourceOrigin⟩ :=
    (origins source).mp sourceIncident
  obtain ⟨targetVar, targetMember, targetOrigin⟩ :=
    (origins target).mp targetIncident
  subst items
  simp only [denoteItemSeq_cons, denoteItem_identity,
    denoteItemSeq_nil, and_true] at itemsDenote
  refine ⟨sourceVar, targetVar, sourceOrigin, targetOrigin, ?_⟩
  exact itemsDenote
    (env sig sourceVar) (List.mem_map.mpr ⟨sourceVar, sourceMember, rfl⟩)
    (env sig targetVar) (List.mem_map.mpr ⟨targetVar, targetMember, rfl⟩)

private inductive ItemSeqCarriesEquality
    (source target : Var ctx sig) :
    ItemSeq definitions ctx → Prop
  | head
      (ports : List (Var ctx sig))
      (atLeastTwo : 2 ≤ ports.length)
      (sourceMember : source ∈ ports)
      (targetMember : target ∈ ports)
      (tail : ItemSeq definitions ctx) :
      ItemSeqCarriesEquality source target
        (.cons (.identity sig ports atLeastTwo) tail)
  | tail
      (head : Item definitions ctx)
      {tail : ItemSeq definitions ctx}
      (carried : ItemSeqCarriesEquality source target tail) :
      ItemSeqCarriesEquality source target (.cons head tail)

private theorem ItemSeqCarriesEquality.values_equal
    {sig : Sig}
    {source target : Var ctx sig}
    {items : ItemSeq definitions ctx}
    (carried : ItemSeqCarriesEquality source target items)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre ctx)
    (denotes : denoteItemSeq pre definitionEnv env items) :
    env sig source = env sig target := by
  induction carried with
  | head ports atLeastTwo sourceMember targetMember tail =>
      exact denotes.1
        (env sig source) (List.mem_map.mpr ⟨source, sourceMember, rfl⟩)
        (env sig target) (List.mem_map.mpr ⟨target, targetMember, rfl⟩)
  | tail head carried induction =>
      exact induction denotes.2

private def ItemSeqCarriesEquality.prepend :
    (leading : ItemSeq definitions ctx) →
      {items : ItemSeq definitions ctx} →
      ItemSeqCarriesEquality source target items →
      ItemSeqCarriesEquality source target (leading.append items)
  | .nil, _, carried => carried
  | .cons item rest, _, carried =>
      .tail item (prepend rest carried)

private def ItemSeqCarriesEquality.append
    {items : ItemSeq definitions ctx}
    (carried : ItemSeqCarriesEquality source target items)
    (suffix : ItemSeq definitions ctx) :
    ItemSeqCarriesEquality source target (items.append suffix) := by
  induction carried with
  | head ports two sourceMember targetMember tail =>
      exact .head ports two sourceMember targetMember (tail.append suffix)
  | tail head nested induction =>
      exact .tail head induction

private structure EqualityGuard (ctx : List Sig) where
  sig : Sig
  source : Var ctx sig
  target : Var ctx sig

namespace EqualityGuard

def rename
    (rho : WireRenaming sourceCtx targetCtx)
    (guard : EqualityGuard sourceCtx) :
    EqualityGuard targetCtx :=
  { sig := guard.sig
    source := rho guard.source
    target := rho guard.target }

def Holds
    (env : Env pre ctx)
    (guard : EqualityGuard ctx) : Prop :=
  env guard.sig guard.source = env guard.sig guard.target

@[simp] theorem holds_rename
    (rho : WireRenaming sourceCtx targetCtx)
    (env : Env pre targetCtx)
    (guard : EqualityGuard sourceCtx) :
    Holds env (guard.rename rho) =
      Holds (Env.comp env rho) guard :=
  rfl

@[simp] theorem rename_id (guard : EqualityGuard ctx) :
    guard.rename (fun value => value) = guard := by
  cases guard
  rfl

end EqualityGuard

private structure ItemSeqCarriesEqualities
    (items : ItemSeq definitions ctx) where
  guards : List (EqualityGuard ctx)
  carried :
    ∀ guard ∈ guards,
      ItemSeqCarriesEquality guard.source guard.target items

namespace ItemSeqCarriesEqualities

def empty (items : ItemSeq definitions ctx) :
    ItemSeqCarriesEqualities items :=
  { guards := []
    carried := by simp }

end ItemSeqCarriesEqualities

private theorem itemSeqCarriesEqualities_values_equal
    {definitions : List (List Sig)}
    {ctx : List Sig}
    {items : ItemSeq definitions ctx}
    (fixed : ItemSeqCarriesEqualities items)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre ctx)
    (denotes : denoteItemSeq pre definitionEnv env items) :
    ∀ (guard : EqualityGuard ctx), guard ∈ fixed.guards →
      EqualityGuard.Holds env guard := by
  intro guard member
  exact (fixed.carried guard member).values_equal
    pre definitionEnv env denotes

private inductive ContextCarriesEqualities :
    {holeCtx outerCtx : List Sig} →
      DiagramContext definitions holeCtx outerCtx → Type
  | hole : ContextCarriesEqualities (.hole : DiagramContext definitions ctx ctx)
  | surround
      (leading : ItemSeq definitions outerCtx)
      (inner : DiagramContext definitions holeCtx outerCtx)
      (suffix : ItemSeq definitions outerCtx)
      (localFixed : ItemSeqCarriesEqualities leading)
      (nested : ContextCarriesEqualities inner) :
      ContextCarriesEqualities (.surround leading inner suffix)
  | cut
      (inner : DiagramContext definitions holeCtx outerCtx)
      (nested : ContextCarriesEqualities inner) :
      ContextCarriesEqualities (.cut inner)
  | bind
      (bound : Sig)
      (inner : DiagramContext definitions holeCtx (bound :: outerCtx))
      (nested : ContextCarriesEqualities inner) :
      ContextCarriesEqualities (.bind bound inner)

namespace ContextCarriesEqualities

def guards :
    {context : DiagramContext definitions holeCtx outerCtx} →
      ContextCarriesEqualities context →
      List (EqualityGuard holeCtx)
  | _, .hole => []
  | _, .surround _ inner _ localFixed nested =>
      localFixed.guards.map
          (EqualityGuard.rename (contextLiftOuter inner)) ++
        nested.guards
  | _, .cut _ nested => nested.guards
  | _, .bind _ _ nested => nested.guards

private theorem equivalenceWithKnown
    {context : DiagramContext definitions holeCtx outerCtx}
    (carried : ContextCarriesEqualities context)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (known : List (EqualityGuard outerCtx))
    (left right : Region definitions holeCtx)
    (bodyEquiv :
      ∀ holeEnv : Env pre holeCtx,
        (∀ guard ∈
              known.map
                (EqualityGuard.rename (contextLiftOuter context)) ++
              carried.guards,
          EqualityGuard.Holds holeEnv guard) →
          (denoteRegion pre definitionEnv holeEnv left ↔
            denoteRegion pre definitionEnv holeEnv right))
    (outerEnv : Env pre outerCtx)
    (knownEqual :
      ∀ guard ∈ known, EqualityGuard.Holds outerEnv guard) :
    denoteRegion pre definitionEnv outerEnv (context.fill left) ↔
      denoteRegion pre definitionEnv outerEnv (context.fill right) := by
  induction carried with
  | hole =>
      apply bodyEquiv outerEnv
      intro guard member
      exact knownEqual guard (by
        simpa [guards, contextLiftOuter] using member)
  | @surround holeCtx outerCtx leading inner suffix localFixed nested induction =>
      simp only [DiagramContext.fill, Region.denote_surround]
      constructor
      · rintro ⟨leadingDenotes, innerDenotes, suffixDenotes⟩
        have localEqual :=
          itemSeqCarriesEqualities_values_equal localFixed
            pre definitionEnv outerEnv leadingDenotes
        have middle :=
          induction (known := known ++ localFixed.guards)
            (left := left) (right := right)
            (fun holeEnv allEqual =>
              bodyEquiv holeEnv (by
                intro guard member
                apply allEqual guard
                simpa only [guards, List.map_append,
                  List.append_assoc] using member))
            outerEnv
            (by
              intro guard member
              simp only [List.mem_append] at member
              exact member.elim
                (fun knownMember => knownEqual guard knownMember)
                (fun localMember => localEqual guard localMember))
        exact ⟨leadingDenotes, middle.mp innerDenotes, suffixDenotes⟩
      · rintro ⟨leadingDenotes, innerDenotes, suffixDenotes⟩
        have localEqual :=
          itemSeqCarriesEqualities_values_equal localFixed
            pre definitionEnv outerEnv leadingDenotes
        have middle :=
          induction (known := known ++ localFixed.guards)
            (left := left) (right := right)
            (fun holeEnv allEqual =>
              bodyEquiv holeEnv (by
                intro guard member
                apply allEqual guard
                simpa only [guards, List.map_append,
                  List.append_assoc] using member))
            outerEnv
            (by
              intro guard member
              simp only [List.mem_append] at member
              exact member.elim
                (fun knownMember => knownEqual guard knownMember)
                (fun localMember => localEqual guard localMember))
        exact ⟨leadingDenotes, middle.mpr innerDenotes, suffixDenotes⟩
  | cut inner nested induction =>
      simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
        denoteItem, and_true]
      exact not_congr
        (induction (known := known) (left := left) (right := right)
          (fun holeEnv allEqual =>
            bodyEquiv holeEnv (by
              intro guard member
              exact allEqual guard member))
          outerEnv knownEqual)
  | @bind holeCtx outerCtx bound inner nested induction =>
      simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
        denoteItem, and_true]
      apply exists_congr
      intro value
      let liftOuter : WireRenaming outerCtx (bound :: outerCtx) :=
        fun {_} wire => .there wire
      let liftedKnown : List (EqualityGuard (bound :: outerCtx)) :=
        known.map (EqualityGuard.rename liftOuter)
      apply induction (known := liftedKnown) (left := left) (right := right)
        (fun holeEnv allEqual =>
          bodyEquiv holeEnv (by
            intro guard member
            apply allEqual guard
            simpa only [liftedKnown, liftOuter, List.map_map,
              Function.comp_def] using
              member))
        (outerEnv.extend value)
      intro guard member
      simp only [liftedKnown, List.mem_map] at member
      obtain ⟨original, originalMember, rfl⟩ := member
      exact knownEqual original originalMember

private theorem equivalence
    {context : DiagramContext definitions holeCtx outerCtx}
    (carried : ContextCarriesEqualities context)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (left right : Region definitions holeCtx)
    (bodyEquiv :
      ∀ holeEnv : Env pre holeCtx,
        (∀ guard ∈ carried.guards,
          EqualityGuard.Holds holeEnv guard) →
          (denoteRegion pre definitionEnv holeEnv left ↔
            denoteRegion pre definitionEnv holeEnv right))
    (outerEnv : Env pre outerCtx) :
    denoteRegion pre definitionEnv outerEnv (context.fill left) ↔
      denoteRegion pre definitionEnv outerEnv (context.fill right) := by
  apply carried.equivalenceWithKnown pre definitionEnv [] left right
    (fun holeEnv allEqual => bodyEquiv holeEnv (by
      intro guard member
      apply allEqual guard
      simpa only [List.map_nil, List.nil_append] using member))
    outerEnv
  simp

end ContextCarriesEqualities

private theorem compileNodes?_cons_eq_singleton_bind
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (nodes : List diagram.NodeId) :
    ConcreteElaboration.compileNodes? definitions diagram context
        (node :: nodes) =
      (do
        let headItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context [node]
        let tailItems ←
          ConcreteElaboration.compileNodes? definitions diagram
            context nodes
        pure (headItems.append tailItems)) := by
  simp [ConcreteElaboration.compileNodes?, ItemSeq.append,
    Option.bind_assoc]

private theorem compileNodes?_carries_identity
    {definitions : List (List Sig)}
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (context : ConcreteElaboration.WireContext diagram)
    (nodes : List diagram.NodeId)
    (identity : diagram.NodeId)
    {region : diagram.RegionId}
    {sig : Sig}
    {arity : Nat}
    (nodeData : diagram.nodes identity = .identity region sig arity)
    (identityMember : identity ∈ nodes)
    (source target : diagram.WireId)
    (sourceIncident : source ∈ diagram.identityIncidentWires identity)
    (targetIncident : target ∈ diagram.identityIncidentWires identity)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions diagram context nodes =
        some items) :
    ∃ (sourceVar targetVar : Var context.sigs sig),
      ConcreteElaboration.WireContext.origin diagram context.ids sourceVar =
          source ∧
        ConcreteElaboration.WireContext.origin diagram context.ids targetVar =
          target ∧
        ItemSeqCarriesEquality sourceVar targetVar items := by
  induction nodes generalizing items with
  | nil => simp at identityMember
  | cons head tail induction =>
      simp only [List.mem_cons] at identityMember
      rw [compileNodes?_cons_eq_singleton_bind] at compiled
      cases headEquation :
          ConcreteElaboration.compileNodes? definitions diagram context
            [head] with
      | none =>
          simp [headEquation] at compiled
      | some headItems =>
          cases tailEquation :
              ConcreteElaboration.compileNodes? definitions diagram context
                tail with
          | none =>
              simp [headEquation, tailEquation] at compiled
          | some tailItems =>
              have itemsEquality :
                  headItems.append tailItems = items :=
                Option.some.inj
                  (by simpa [headEquation, tailEquation] using compiled)
              subst items
              rcases identityMember with same | tailMember
              · subst head
                obtain ⟨ports, two, identityItems, origins⟩ :=
                  ConcreteElaboration.compileNodes?_identity_origins diagram
                    wellFormed context identity nodeData headEquation
                subst headItems
                obtain ⟨sourceVar, sourceMember, sourceOrigin⟩ :=
                  (origins source).mp sourceIncident
                obtain ⟨targetVar, targetMember, targetOrigin⟩ :=
                  (origins target).mp targetIncident
                exact
                  ⟨sourceVar, targetVar, sourceOrigin, targetOrigin,
                    .head ports two sourceMember targetMember tailItems⟩
              · obtain ⟨sourceVar, targetVar, sourceOrigin, targetOrigin,
                    carried⟩ :=
                  induction tailMember tailItems tailEquation
                exact
                  ⟨sourceVar, targetVar, sourceOrigin, targetOrigin,
                    carried.prepend headItems⟩

private inductive ContextCarriesEquality
    (source target : Var holeCtx sig) :
    DiagramContext definitions holeCtx outerCtx → Type
  | checkpoint
      (leading : ItemSeq definitions checkpointCtx)
      (inner : DiagramContext definitions holeCtx checkpointCtx)
      (suffix : ItemSeq definitions checkpointCtx)
      (checkpointSource checkpointTarget : Var checkpointCtx sig)
      (carried :
        ItemSeqCarriesEquality checkpointSource checkpointTarget leading)
      (sourceExact :
        contextLiftOuter inner checkpointSource = source)
      (targetExact :
        contextLiftOuter inner checkpointTarget = target) :
      ContextCarriesEquality source target
        (.surround leading inner suffix)
  | surround
      (leading : ItemSeq definitions outerCtx)
      {inner : DiagramContext definitions holeCtx outerCtx}
      (suffix : ItemSeq definitions outerCtx)
      (carried : ContextCarriesEquality source target inner) :
      ContextCarriesEquality source target
        (.surround leading inner suffix)
  | cut
      {inner : DiagramContext definitions holeCtx outerCtx}
      (carried : ContextCarriesEquality source target inner) :
      ContextCarriesEquality source target (.cut inner)
  | bind
      (bound : Sig)
      {inner :
        DiagramContext definitions holeCtx (bound :: outerCtx)}
      (carried : ContextCarriesEquality source target inner) :
      ContextCarriesEquality source target (.bind bound inner)

private theorem ContextCarriesEquality.equivalence
    {sig : Sig}
    {source target : Var holeCtx sig}
    {context : DiagramContext definitions holeCtx outerCtx}
    (carried : ContextCarriesEquality source target context)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (left right : Region definitions holeCtx)
    (bodyEquiv :
      ∀ holeEnv : Env pre holeCtx,
        holeEnv sig source = holeEnv sig target →
          (denoteRegion pre definitionEnv holeEnv left ↔
            denoteRegion pre definitionEnv holeEnv right))
    (outerEnv : Env pre outerCtx) :
    denoteRegion pre definitionEnv outerEnv (context.fill left) ↔
      denoteRegion pre definitionEnv outerEnv (context.fill right) := by
  induction carried with
  | checkpoint leading inner suffix checkpointSource checkpointTarget
      fixed sourceExact targetExact =>
      simp only [DiagramContext.fill, Region.denote_surround]
      constructor
      · rintro ⟨leadingDenotes, innerDenotes, suffixDenotes⟩
        have equal :=
          fixed.values_equal pre definitionEnv outerEnv leadingDenotes
        have middle :=
          context_equiv_of_outer_eq inner checkpointSource checkpointTarget
            pre definitionEnv left right
            (fun holeEnv liftedEqual =>
              bodyEquiv holeEnv
                (by simpa [sourceExact, targetExact] using liftedEqual))
            outerEnv equal
        exact ⟨leadingDenotes, middle.mp innerDenotes, suffixDenotes⟩
      · rintro ⟨leadingDenotes, innerDenotes, suffixDenotes⟩
        have equal :=
          fixed.values_equal pre definitionEnv outerEnv leadingDenotes
        have middle :=
          context_equiv_of_outer_eq inner checkpointSource checkpointTarget
            pre definitionEnv left right
            (fun holeEnv liftedEqual =>
              bodyEquiv holeEnv
                (by simpa [sourceExact, targetExact] using liftedEqual))
            outerEnv equal
        exact ⟨leadingDenotes, middle.mpr innerDenotes, suffixDenotes⟩
  | surround leading suffix carried induction =>
      simp only [DiagramContext.fill, Region.denote_surround]
      exact and_congr Iff.rfl (and_congr
        (induction outerEnv) Iff.rfl)
  | cut carried induction =>
      simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
        denoteItem, and_true]
      exact not_congr
        (induction outerEnv)
  | bind bound carried induction =>
      simp only [DiagramContext.fill, denoteRegion, denoteItemSeq,
        denoteItem, and_true]
      apply exists_congr
      intro value
      exact induction (outerEnv.extend value)

private def ItemSeqCarriesEqualities.combine
    {items : ItemSeq definitions ctx}
    (left right : ItemSeqCarriesEqualities items) :
    ItemSeqCarriesEqualities items :=
  { guards := left.guards ++ right.guards
    carried := by
      intro guard member
      simp only [List.mem_append] at member
      exact member.elim (left.carried guard) (right.carried guard) }

private def ContextCarriesEqualities.emptyFor :
    (context : DiagramContext definitions holeCtx outerCtx) →
      ContextCarriesEqualities context
  | .hole => .hole
  | .surround leading inner suffix =>
      .surround leading inner suffix
        (ItemSeqCarriesEqualities.empty leading)
        (emptyFor inner)
  | .cut inner => .cut inner (emptyFor inner)
  | .bind bound inner => .bind bound inner (emptyFor inner)

@[simp] private theorem ContextCarriesEqualities.emptyFor_guards
    (context : DiagramContext definitions holeCtx outerCtx) :
    (ContextCarriesEqualities.emptyFor context).guards = [] := by
  induction context with
  | hole => rfl
  | surround leading inner suffix induction =>
      simp [ContextCarriesEqualities.emptyFor,
        ContextCarriesEqualities.guards, induction,
        ItemSeqCarriesEqualities.empty]
  | cut inner induction =>
      simpa [ContextCarriesEqualities.emptyFor,
        ContextCarriesEqualities.guards] using induction
  | bind bound inner induction =>
      simpa [ContextCarriesEqualities.emptyFor,
        ContextCarriesEqualities.guards] using induction

private def ContextCarriesEqualities.combine :
    {context : DiagramContext definitions holeCtx outerCtx} →
      ContextCarriesEqualities context →
      ContextCarriesEqualities context →
      ContextCarriesEqualities context
  | _, .hole, .hole => .hole
  | _, .surround leading inner suffix leftLocal leftNested,
      .surround _ _ _ rightLocal rightNested =>
      .surround leading inner suffix
        (leftLocal.combine rightLocal)
        (leftNested.combine rightNested)
  | _, .cut inner leftNested, .cut _ rightNested =>
      .cut inner (leftNested.combine rightNested)
  | _, .bind bound inner leftNested, .bind _ _ rightNested =>
      .bind bound inner (leftNested.combine rightNested)

private theorem ContextCarriesEqualities.mem_combine_left
    {context : DiagramContext definitions holeCtx outerCtx}
    (left right : ContextCarriesEqualities context)
    {guard : EqualityGuard holeCtx}
    (member : guard ∈ left.guards) :
    guard ∈ (left.combine right).guards := by
  induction left with
  | hole =>
      simp [ContextCarriesEqualities.guards] at member
  | surround leading inner suffix leftLocal leftNested induction =>
      cases right with
      | surround _ _ _ rightLocal rightNested =>
          simp only [ContextCarriesEqualities.combine,
            ContextCarriesEqualities.guards,
            List.mem_append, List.mem_map] at member ⊢
          rcases member with localMember | nestedMember
          · left
            obtain ⟨localGuard, localMember, exactGuard⟩ := localMember
            refine ⟨localGuard, ?_, exactGuard⟩
            simp only [ItemSeqCarriesEqualities.combine,
              List.mem_append]
            exact .inl localMember
          · right
            exact induction rightNested nestedMember
  | cut inner leftNested induction =>
      cases right with
      | cut _ rightNested =>
          exact induction rightNested member
  | bind bound inner leftNested induction =>
      cases right with
      | bind _ _ rightNested =>
          exact induction rightNested member

private theorem ContextCarriesEqualities.mem_combine_right
    {context : DiagramContext definitions holeCtx outerCtx}
    (left right : ContextCarriesEqualities context)
    {guard : EqualityGuard holeCtx}
    (member : guard ∈ right.guards) :
    guard ∈ (left.combine right).guards := by
  induction left with
  | hole =>
      cases right
      simp [ContextCarriesEqualities.guards] at member
  | surround leading inner suffix leftLocal leftNested induction =>
      cases right with
      | surround _ _ _ rightLocal rightNested =>
          simp only [ContextCarriesEqualities.combine,
            ContextCarriesEqualities.guards,
            List.mem_append, List.mem_map] at member ⊢
          rcases member with localMember | nestedMember
          · left
            obtain ⟨localGuard, localMember, exactGuard⟩ := localMember
            refine ⟨localGuard, ?_, exactGuard⟩
            simp only [ItemSeqCarriesEqualities.combine,
              List.mem_append]
            exact .inr localMember
          · right
            exact induction rightNested nestedMember
  | cut inner leftNested induction =>
      cases right with
      | cut _ rightNested =>
          exact induction rightNested member
  | bind bound inner leftNested induction =>
      cases right with
      | bind _ _ rightNested =>
          exact induction rightNested member

private def ContextCarriesEqualities.ofSingle
    {source target : Var holeCtx sig}
    {context : DiagramContext definitions holeCtx outerCtx}
    (single : ContextCarriesEquality source target context) :
    ContextCarriesEqualities context :=
  match single with
  | .checkpoint leading inner suffix checkpointSource checkpointTarget
      fixed sourceExact targetExact =>
      .surround leading inner suffix
        { guards :=
            [{ sig := sig
               source := checkpointSource
               target := checkpointTarget }]
          carried := by
            intro guard member
            simp only [List.mem_singleton] at member
            subst guard
            exact fixed }
        (emptyFor inner)
  | .surround leading suffix nested =>
      .surround leading _ suffix
        (ItemSeqCarriesEqualities.empty leading)
        (ofSingle nested)
  | .cut nested => .cut _ (ofSingle nested)
  | .bind bound nested => .bind bound _ (ofSingle nested)

private theorem ContextCarriesEqualities.ofSingle_guard
    {source target : Var holeCtx sig}
    {context : DiagramContext definitions holeCtx outerCtx}
    (single : ContextCarriesEquality source target context) :
    ({ sig := sig, source := source, target := target } :
        EqualityGuard holeCtx) ∈
      (ContextCarriesEqualities.ofSingle single).guards := by
  induction single with
  | checkpoint leading inner suffix checkpointSource checkpointTarget fixed
      sourceExact targetExact =>
      simp only [ContextCarriesEqualities.ofSingle,
        ContextCarriesEqualities.guards, List.map_singleton,
        ContextCarriesEqualities.emptyFor_guards, List.append_nil,
        List.mem_singleton]
      rw [← sourceExact, ← targetExact]
      rfl
  | surround leading suffix nested induction =>
      simpa [ContextCarriesEqualities.ofSingle,
        ContextCarriesEqualities.guards,
        ItemSeqCarriesEqualities.empty] using induction
  | cut nested induction =>
      simpa [ContextCarriesEqualities.ofSingle,
        ContextCarriesEqualities.guards] using induction
  | bind bound nested induction =>
      simpa [ContextCarriesEqualities.ofSingle,
        ContextCarriesEqualities.guards] using induction

private theorem compileSiblingFrame?_shape
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (fuel : Nat)
    (outer : ConcreteElaboration.WireContext diagram)
    (target : diagram.RegionId)
    (nested frame :
      RegionFrame definitions diagram outer)
    (leading : ItemSeq definitions outer.sigs)
    (children : List diagram.RegionId)
    (accepted :
      compileSiblingFrame? definitions diagram fuel
          outer target nested leading children =
        some frame) :
    ∃ (before suffix : ItemSeq definitions outer.sigs),
      frame =
        { visible := nested.visible
          siteBody := nested.siteBody
          context :=
            .surround (leading.append before)
              (.cut nested.context) suffix } := by
  induction children generalizing leading frame with
  | nil =>
      simp [compileSiblingFrame?] at accepted
  | cons child tail induction =>
      unfold compileSiblingFrame? at accepted
      split at accepted
      · cases suffixEquation :
          ConcreteElaboration.compileChildrenWith? definitions diagram
            (ConcreteElaboration.compileRegion? definitions diagram fuel)
            outer tail with
        | none =>
            simp [suffixEquation] at accepted
        | some suffix =>
            refine ⟨.nil, suffix, ?_⟩
            exact Option.some.inj
              (by simpa [suffixEquation, ItemSeq.append] using accepted)
                |>.symm
      · cases bodyEquation :
          ConcreteElaboration.compileRegion? definitions diagram fuel child
            outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            obtain ⟨before, suffix, shape⟩ := induction
              (frame := frame)
              (leading :=
                leading.append (.cons (.cut body) .nil))
              (by simpa [bodyEquation] using accepted)
            refine
              ⟨(ItemSeq.cons (.cut body) .nil).append before,
                suffix, ?_⟩
            simpa only [ItemSeq.append_assoc] using shape

private noncomputable def ContextCarriesEquality.bindContextFor
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    {inner :
      DiagramContext definitions holeCtx
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig)}
    (carried : ContextCarriesEquality source target inner) :
    ContextCarriesEquality source target
      (bindContextFor
        diagram outerIds localIds inner) := by
  induction localIds with
  | nil => exact carried
  | cons head tail induction =>
      exact induction (.bind (diagram.wires head).sig carried)

private theorem bindContextFor_context_origin
    (diagram : ConcreteDiagram definitionCount)
    (outerIds localIds : List diagram.WireId)
    (visible : ConcreteElaboration.WireContext diagram)
    (inner :
      DiagramContext definitions visible.sigs
        ((localIds ++ outerIds).map fun wire =>
          (diagram.wires wire).sig))
    (innerOrigin :
      ∀ {sig} (value :
          Var
            ((localIds ++ outerIds).map fun wire =>
              (diagram.wires wire).sig)
            sig),
        ConcreteElaboration.WireContext.origin diagram visible.ids
            (contextLiftOuter inner value) =
          ConcreteElaboration.WireContext.origin diagram
            (localIds ++ outerIds) value) :
    ∀ {sig} (value :
        Var
          (outerIds.map fun wire => (diagram.wires wire).sig)
          sig),
      ConcreteElaboration.WireContext.origin diagram visible.ids
          (contextLiftOuter
            (bindContextFor
              diagram outerIds localIds inner)
            value) =
        ConcreteElaboration.WireContext.origin diagram outerIds value := by
  induction localIds with
  | nil =>
      intro sig value
      exact innerOrigin value
  | cons head tail induction =>
      apply induction (.bind (diagram.wires head).sig inner)
      intro sig value
      have lifted := innerOrigin (Var.there value)
      exact lifted

private theorem compileRegionFrame?_context_origin
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (site : diagram.RegionId) :
    ∀ (fuel : Nat) (region : diagram.RegionId)
      (outer : ConcreteElaboration.WireContext diagram)
      (frame : RegionFrame definitions diagram outer),
      compileRegionFrame? definitions diagram site fuel region outer =
          some frame →
        ∀ {sig} (value : Var outer.sigs sig),
          ConcreteElaboration.WireContext.origin diagram frame.visible.ids
              (contextLiftOuter frame.context value) =
            ConcreteElaboration.WireContext.origin diagram outer.ids value := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer frame accepted
      simp [compileRegionFrame?] at accepted
  | succ fuel induction =>
      intro region outer frame accepted
      unfold compileRegionFrame? at accepted
      simp only [] at accepted
      split at accepted
      · cases bodyEquation :
          compileRegionBody? definitions diagram fuel region outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            have frameEquality :
                ({ visible := outer.extend region
                   siteBody := body
                   context :=
                     bindContextFor diagram outer.ids
                       (diagram.wiresAt region) .hole } :
                  RegionFrame definitions diagram outer) =
                frame :=
              Option.some.inj
                (by simpa [bodyEquation] using accepted)
            subst frame
            apply bindContextFor_context_origin diagram outer.ids
              (diagram.wiresAt region) (outer.extend region) .hole
            intro sig value
            exact rfl
      · cases nodesEquation :
          ConcreteElaboration.compileNodes? definitions diagram
            (outer.extend region) (diagram.nodesAt region) with
        | none =>
            simp [nodesEquation] at accepted
        | some nodes =>
            cases childEquation :
                (diagram.childrenOf region).find?
                  (fun candidate =>
                    decide (diagram.Encloses candidate site)) with
            | none =>
                simp [nodesEquation, childEquation] at accepted
            | some child =>
                cases nestedEquation :
                    compileRegionFrame? definitions diagram site fuel child
                      (outer.extend region) with
                | none =>
                    simp [nodesEquation, childEquation, nestedEquation]
                      at accepted
                | some nested =>
                    cases aroundEquation :
                        compileSiblingFrame? definitions diagram fuel
                          (outer.extend region) child nested nodes
                          (diagram.childrenOf region) with
                    | none =>
                        simp [nodesEquation, childEquation, nestedEquation,
                          aroundEquation] at accepted
                    | some around =>
                        have frameEquality :
                            ({ visible := around.visible
                               siteBody := around.siteBody
                               context :=
                                 bindContextFor diagram outer.ids
                                   (diagram.wiresAt region)
                                   around.context } :
                              RegionFrame definitions diagram outer) =
                            frame :=
                          Option.some.inj
                            (by simpa [nodesEquation, childEquation,
                                nestedEquation, aroundEquation] using
                              accepted)
                        subst frame
                        obtain ⟨before, suffix, shape⟩ :=
                          compileSiblingFrame?_shape definitions diagram fuel
                            (outer.extend region) child nested around nodes
                            (diagram.childrenOf region) aroundEquation
                        subst around
                        apply bindContextFor_context_origin diagram outer.ids
                          (diagram.wiresAt region) nested.visible
                          (.surround (nodes.append before)
                            (.cut nested.context) suffix)
                        intro sig value
                        exact induction child (outer.extend region) nested
                          nestedEquation value

private theorem compileRegionFrame?_visible_nodup
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (site : diagram.RegionId) :
    ∀ (fuel : Nat) (region : diagram.RegionId)
      (outer : ConcreteElaboration.WireContext diagram)
      (frame : RegionFrame definitions diagram outer),
      ConcreteElaboration.ContextAbove diagram outer region →
      compileRegionFrame? definitions diagram site fuel region outer =
          some frame →
        frame.visible.ids.Nodup := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer frame above accepted
      simp [compileRegionFrame?] at accepted
  | succ fuel induction =>
      intro region outer frame above accepted
      unfold compileRegionFrame? at accepted
      simp only [] at accepted
      split at accepted
      · cases bodyEquation :
          compileRegionBody? definitions diagram fuel region outer with
        | none =>
            simp [bodyEquation] at accepted
        | some body =>
            have frameEquality :
                ({ visible := outer.extend region
                   siteBody := body
                   context :=
                     bindContextFor diagram outer.ids
                       (diagram.wiresAt region) .hole } :
                  RegionFrame definitions diagram outer) =
                frame :=
              Option.some.inj
                (by simpa [bodyEquation] using accepted)
            subst frame
            exact ConcreteElaboration.extend_nodup definitions diagram
              wellFormed outer region above
      · cases nodesEquation :
          ConcreteElaboration.compileNodes? definitions diagram
            (outer.extend region) (diagram.nodesAt region) with
        | none =>
            simp [nodesEquation] at accepted
        | some nodes =>
            cases childEquation :
                (diagram.childrenOf region).find?
                  (fun candidate =>
                    decide (diagram.Encloses candidate site)) with
            | none =>
                simp [nodesEquation, childEquation] at accepted
            | some child =>
                have childMember :
                    child ∈ diagram.childrenOf region :=
                  List.mem_of_find?_eq_some childEquation
                have childData :
                    diagram.regions child = .cut region :=
                  ConcreteElaboration.mem_childrenOf
                    diagram region child childMember
                have extendedAbove :=
                  ConcreteElaboration.extend_above_child definitions diagram
                    wellFormed outer region child above childData
                cases nestedEquation :
                    compileRegionFrame? definitions diagram site fuel child
                      (outer.extend region) with
                | none =>
                    simp [nodesEquation, childEquation, nestedEquation]
                      at accepted
                | some nested =>
                    have nestedNodup :=
                      induction child (outer.extend region) nested
                        extendedAbove nestedEquation
                    cases aroundEquation :
                        compileSiblingFrame? definitions diagram fuel
                          (outer.extend region) child nested nodes
                          (diagram.childrenOf region) with
                    | none =>
                        simp [nodesEquation, childEquation, nestedEquation,
                          aroundEquation] at accepted
                    | some around =>
                        have frameEquality :
                            ({ visible := around.visible
                               siteBody := around.siteBody
                               context :=
                                 bindContextFor diagram outer.ids
                                   (diagram.wiresAt region)
                                   around.context } :
                              RegionFrame definitions diagram outer) =
                            frame :=
                          Option.some.inj
                            (by simpa [nodesEquation, childEquation,
                                nestedEquation, aroundEquation] using
                              accepted)
                        subst frame
                        obtain ⟨before, suffix, shape⟩ :=
                          compileSiblingFrame?_shape definitions diagram fuel
                            (outer.extend region) child nested around nodes
                            (diagram.childrenOf region) aroundEquation
                        subst around
                        exact nestedNodup

private theorem retarget_climb_to_root_unique
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region : diagram.RegionId}
    {left right : Nat}
    (leftClimb : diagram.climb left region = some diagram.root)
    (rightClimb : diagram.climb right region = some diagram.root) :
    left = right := by
  induction left generalizing right region with
  | zero =>
      have regionRoot : region = diagram.root := by
        simpa [ConcreteDiagram.climb] using leftClimb
      subst region
      cases right with
      | zero => rfl
      | succ right =>
          have rootData := wellFormed.root_is_sheet
          change diagram.regions diagram.root = .sheet at rootData
          rw [ConcreteDiagram.climb, rootData] at rightClimb
          contradiction
  | succ left induction =>
      cases right with
      | zero =>
          have regionRoot : region = diagram.root := by
            simpa [ConcreteDiagram.climb] using rightClimb
          subst region
          have rootData := wellFormed.root_is_sheet
          change diagram.regions diagram.root = .sheet at rootData
          rw [ConcreteDiagram.climb, rootData] at leftClimb
          contradiction
      | succ right =>
          cases regionData : diagram.regions region with
          | sheet =>
              simp [ConcreteDiagram.climb, regionData] at leftClimb
          | cut parent =>
              have leftParent :
                  diagram.climb left parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using leftClimb
              have rightParent :
                  diagram.climb right parent = some diagram.root := by
                simpa [ConcreteDiagram.climb, regionData] using rightClimb
              exact congrArg Nat.succ
                (induction leftParent rightParent)

private theorem retarget_climb_add
    (diagram : ConcreteDiagram definitionCount)
    (first second : Nat)
    (region : diagram.RegionId) :
    diagram.climb (first + second) region =
      (diagram.climb first region).bind (diagram.climb second) := by
  induction first generalizing region with
  | zero => simp
  | succ first induction =>
      cases regionData : diagram.regions region with
      | sheet =>
          simp [Nat.succ_add, ConcreteDiagram.climb, regionData]
      | cut parent =>
          simpa [ConcreteDiagram.climb, regionData, Nat.succ_add] using
            induction parent

private theorem retarget_reaches_root
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (region : diagram.RegionId) :
    ∃ steps : Fin (diagram.regionCount + 1),
      diagram.climb steps region = some diagram.root := by
  have checked :=
    (List.all_eq_true.mp wellFormed.all_regions_reach_root)
      region (Data.Finite.mem_allFin region)
  exact
    (ConcreteElaboration.encloses_iff_exists
      diagram diagram.root region).mp (of_decide_eq_true checked)

private theorem retarget_encloses_antisymm
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {left right : diagram.RegionId}
    (leftRight : diagram.Encloses left right)
    (rightLeft : diagram.Encloses right left) :
    left = right := by
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram left right).mp leftRight
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram right left).mp rightLeft
  obtain ⟨rootSteps, rootClimb⟩ :=
    retarget_reaches_root definitions diagram wellFormed left
  have loop :
      diagram.climb (rightSteps.val + leftSteps.val) left =
        some left := by
    rw [retarget_climb_add, rightClimb]
    exact leftClimb
  have longerRoot :
      diagram.climb
          ((rightSteps.val + leftSteps.val) + rootSteps.val)
          left =
        some diagram.root := by
    rw [retarget_climb_add, loop]
    exact rootClimb
  have sameDepth :=
    retarget_climb_to_root_unique definitions diagram wellFormed
      longerRoot rootClimb
  have rightZero : rightSteps.val = 0 := by omega
  have exactRight := rightClimb
  rw [rightZero] at exactRight
  simpa [ConcreteDiagram.climb] using exactRight

private theorem retarget_encloses_comparable
    (diagram : ConcreteDiagram definitionCount)
    {left right descendant : diagram.RegionId}
    (leftEncloses : diagram.Encloses left descendant)
    (rightEncloses : diagram.Encloses right descendant) :
    diagram.Encloses left right ∨ diagram.Encloses right left := by
  obtain ⟨leftSteps, leftClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram left descendant).mp leftEncloses
  obtain ⟨rightSteps, rightClimb⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram right descendant).mp rightEncloses
  by_cases leftBefore : leftSteps.val ≤ rightSteps.val
  · right
    apply
      (ConcreteElaboration.encloses_iff_exists
        diagram right left).mpr
    let remaining := rightSteps.val - leftSteps.val
    have sum : leftSteps.val + remaining = rightSteps.val := by
      omega
    have remainingBound :
        remaining < diagram.regionCount + 1 := by
      exact Nat.lt_of_le_of_lt
        (Nat.sub_le _ _) rightSteps.isLt
    refine ⟨⟨remaining, remainingBound⟩, ?_⟩
    have composed :=
      retarget_climb_add diagram leftSteps.val remaining descendant
    rw [sum, leftClimb, rightClimb] at composed
    exact composed.symm
  · left
    apply
      (ConcreteElaboration.encloses_iff_exists
        diagram left right).mpr
    let remaining := leftSteps.val - rightSteps.val
    have sum : rightSteps.val + remaining = leftSteps.val := by
      omega
    have remainingBound :
        remaining < diagram.regionCount + 1 := by
      exact Nat.lt_of_le_of_lt
        (Nat.sub_le _ _) leftSteps.isLt
    refine ⟨⟨remaining, remainingBound⟩, ?_⟩
    have composed :=
      retarget_climb_add diagram rightSteps.val remaining descendant
    rw [sum, rightClimb, leftClimb] at composed
    exact composed.symm

private theorem retarget_encloses_child_split
    (diagram : ConcreteDiagram definitionCount)
    (ancestor child parent : diagram.RegionId)
    (childData : diagram.regions child = .cut parent)
    (encloses : diagram.Encloses ancestor child) :
    ancestor = child ∨ diagram.Encloses ancestor parent := by
  obtain ⟨steps, climbed⟩ :=
    (ConcreteElaboration.encloses_iff_exists
      diagram ancestor child).mp encloses
  cases steps with
  | mk steps bound =>
      cases steps with
      | zero => exact .inl (by simpa using climbed.symm)
      | succ steps =>
          right
          apply
            (ConcreteElaboration.encloses_iff_exists
              diagram ancestor parent).mpr
          exact
            ⟨⟨steps, by omega⟩, by
              simpa [ConcreteDiagram.climb, childData] using climbed⟩

private theorem selected_child_encloses_middle
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    {region child middle site : diagram.RegionId}
    (regionMiddle : diagram.Encloses region middle)
    (middleStrict : middle ≠ region)
    (childData : diagram.regions child = .cut region)
    (childSite : diagram.Encloses child site)
    (middleSite : diagram.Encloses middle site) :
    diagram.Encloses child middle := by
  rcases retarget_encloses_comparable diagram childSite middleSite with
    childMiddle | middleChild
  · exact childMiddle
  · rcases retarget_encloses_child_split diagram middle child region
        childData middleChild with middleIsChild | middleRegion
    · subst middle
      exact ConcreteDiagram.encloses_refl diagram child
    · have same :=
        retarget_encloses_antisymm definitions diagram wellFormed
          regionMiddle middleRegion
      exact False.elim (middleStrict same.symm)

private structure FrameIdentityCarrier
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (outer : ConcreteElaboration.WireContext diagram)
    (frame : RegionFrame definitions diagram outer)
    (sig : Sig)
    (source target : diagram.WireId) where
  sourceVar : Var frame.visible.sigs sig
  targetVar : Var frame.visible.sigs sig
  source_origin :
    ConcreteElaboration.WireContext.origin diagram frame.visible.ids
        sourceVar =
      source
  target_origin :
    ConcreteElaboration.WireContext.origin diagram frame.visible.ids
        targetVar =
      target
  carrier :
    ContextCarriesEquality sourceVar targetVar frame.context

private theorem compileRegionFrame?_carries_identity
    (definitions : List (List Sig))
    (diagram : ConcreteDiagram definitions.length)
    (wellFormed : diagram.WellFormed definitions)
    (site identityRegion : diagram.RegionId)
    (identity : diagram.NodeId)
    (sig : Sig)
    (arity : Nat)
    (nodeData :
      diagram.nodes identity = .identity identityRegion sig arity)
    (identitySite : diagram.Encloses identityRegion site)
    (identityStrict : identityRegion ≠ site)
    (source target : diagram.WireId)
    (sourceIncident : source ∈ diagram.identityIncidentWires identity)
    (targetIncident : target ∈ diagram.identityIncidentWires identity) :
    ∀ (fuel : Nat) (region : diagram.RegionId)
      (outer : ConcreteElaboration.WireContext diagram)
      (frame : RegionFrame definitions diagram outer),
      compileRegionFrame? definitions diagram site fuel region outer =
          some frame →
        diagram.Encloses region identityRegion →
        Nonempty
          (FrameIdentityCarrier definitions diagram outer frame
            sig source target) := by
  intro fuel
  induction fuel with
  | zero =>
      intro region outer frame accepted
      simp [compileRegionFrame?] at accepted
  | succ fuel induction =>
      intro region outer frame accepted regionIdentity
      unfold compileRegionFrame? at accepted
      simp only [] at accepted
      split at accepted
      · rename_i atSite
        subst region
        have same :=
          retarget_encloses_antisymm definitions diagram wellFormed
            regionIdentity identitySite
        exact False.elim (identityStrict same.symm)
      · rename_i notAtSite
        cases nodesEquation :
            ConcreteElaboration.compileNodes? definitions diagram
              (outer.extend region) (diagram.nodesAt region) with
        | none =>
            simp [nodesEquation] at accepted
        | some nodes =>
            cases childEquation :
                (diagram.childrenOf region).find?
                  (fun candidate =>
                    decide (diagram.Encloses candidate site)) with
            | none =>
                simp [nodesEquation, childEquation] at accepted
            | some child =>
                have childMember :
                    child ∈ diagram.childrenOf region :=
                  List.mem_of_find?_eq_some childEquation
                have childData :
                    diagram.regions child = .cut region :=
                  ConcreteElaboration.mem_childrenOf
                    diagram region child childMember
                have childSite :
                    diagram.Encloses child site :=
                  of_decide_eq_true
                    (List.find?_some
                      (p := fun candidate =>
                        decide (diagram.Encloses candidate site))
                      childEquation)
                cases nestedEquation :
                    compileRegionFrame? definitions diagram site fuel child
                      (outer.extend region) with
                | none =>
                    simp [nodesEquation, childEquation, nestedEquation]
                      at accepted
                | some nested =>
                    cases aroundEquation :
                        compileSiblingFrame? definitions diagram fuel
                          (outer.extend region) child nested nodes
                          (diagram.childrenOf region) with
                    | none =>
                        simp [nodesEquation, childEquation, nestedEquation,
                          aroundEquation] at accepted
                    | some around =>
                        have frameEquality :
                            ({ visible := around.visible
                               siteBody := around.siteBody
                               context :=
                                 bindContextFor diagram outer.ids
                                   (diagram.wiresAt region)
                                   around.context } :
                              RegionFrame definitions diagram outer) =
                            frame :=
                          Option.some.inj
                            (by simpa [nodesEquation, childEquation,
                                nestedEquation, aroundEquation] using
                              accepted)
                        subst frame
                        obtain ⟨before, suffix, shape⟩ :=
                          compileSiblingFrame?_shape definitions diagram fuel
                            (outer.extend region) child nested around nodes
                            (diagram.childrenOf region) aroundEquation
                        subst around
                        by_cases identityHere : identityRegion = region
                        · subst region
                          have identityMember :
                              identity ∈ diagram.nodesAt identityRegion := by
                            apply List.mem_filter.mpr
                            refine ⟨Data.Finite.mem_allFin identity, ?_⟩
                            rw [nodeData]
                            simp only [CNode.region, beq_self_eq_true]
                          obtain ⟨checkpointSource, checkpointTarget,
                              sourceOrigin, targetOrigin, fixed⟩ :=
                            compileNodes?_carries_identity diagram wellFormed
                              (outer.extend identityRegion)
                              (diagram.nodesAt identityRegion) identity
                              nodeData identityMember source target
                              sourceIncident targetIncident nodes nodesEquation
                          let sourceVar :=
                            contextLiftOuter nested.context checkpointSource
                          let targetVar :=
                            contextLiftOuter nested.context checkpointTarget
                          have sourceFinalOrigin :
                              ConcreteElaboration.WireContext.origin diagram
                                  nested.visible.ids sourceVar =
                                source := by
                            exact
                              (compileRegionFrame?_context_origin definitions
                                  diagram site fuel child
                                  (outer.extend identityRegion) nested
                                  nestedEquation checkpointSource).trans
                                sourceOrigin
                          have targetFinalOrigin :
                              ConcreteElaboration.WireContext.origin diagram
                                  nested.visible.ids targetVar =
                                target := by
                            exact
                              (compileRegionFrame?_context_origin definitions
                                  diagram site fuel child
                                  (outer.extend identityRegion) nested
                                  nestedEquation checkpointTarget).trans
                                targetOrigin
                          let checkpoint :
                              ContextCarriesEquality sourceVar targetVar
                                (.surround (nodes.append before)
                                  (.cut nested.context) suffix) :=
                            .checkpoint (nodes.append before)
                              (.cut nested.context) suffix checkpointSource
                              checkpointTarget (fixed.append before)
                              rfl rfl
                          exact
                            ⟨{
                              sourceVar := sourceVar
                              targetVar := targetVar
                              source_origin := sourceFinalOrigin
                              target_origin := targetFinalOrigin
                              carrier :=
                                checkpoint.bindContextFor diagram outer.ids
                                  (diagram.wiresAt identityRegion) }⟩
                        · have childIdentity :
                              diagram.Encloses child identityRegion :=
                            selected_child_encloses_middle definitions diagram
                              wellFormed regionIdentity identityHere childData
                              childSite identitySite
                          obtain ⟨nestedResult⟩ :=
                            induction child (outer.extend region) nested
                              nestedEquation childIdentity
                          let aroundCarrier :
                              ContextCarriesEquality
                                nestedResult.sourceVar nestedResult.targetVar
                                (.surround (nodes.append before)
                                  (.cut nested.context) suffix) :=
                            .surround (nodes.append before) suffix
                              (.cut nestedResult.carrier)
                          exact
                            ⟨{
                              sourceVar := nestedResult.sourceVar
                              targetVar := nestedResult.targetVar
                              source_origin := nestedResult.source_origin
                              target_origin := nestedResult.target_origin
                              carrier :=
                                aroundCarrier.bindContextFor diagram outer.ids
                                  (diagram.wiresAt region) }⟩

private theorem SiteCompilation.carries_identity_strict
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site)
    (evidence : IdentityRetarget base site)
    (strict : evidence.identityRegion ≠ site) :
    Nonempty
      (FrameIdentityCarrier definitions base.val
        (ConcreteElaboration.WireContext.empty base.val)
        compiled.frame evidence.identitySig
        evidence.sourceWire evidence.targetWire) := by
  have rootIdentity :
      base.val.Encloses base.val.root evidence.identityRegion := by
    exact of_decide_eq_true
      ((List.all_eq_true.mp base.property.all_regions_reach_root)
        evidence.identityRegion
        (Data.Finite.mem_allFin evidence.identityRegion))
  exact
    compileRegionFrame?_carries_identity definitions base.val base.property
      site evidence.identityRegion evidence.identity evidence.identitySig
      evidence.identityArity evidence.identity_data evidence.dominates strict
      evidence.sourceWire evidence.targetWire evidence.source_incident
      evidence.target_incident (base.val.regionCount + 1) base.val.root
      (ConcreteElaboration.WireContext.empty base.val) compiled.frame
      compiled.frame_generated rootIdentity

private theorem origin_mem
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    {sig : Sig}
    (value :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig) :
    ConcreteElaboration.WireContext.origin diagram ids value ∈ ids := by
  induction ids with
  | nil => nomatch value
  | cons head tail induction =>
      cases value with
      | here => exact List.mem_cons_self
      | there value => exact List.mem_cons_of_mem head (induction value)

private theorem origin_injective
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    {sig : Sig}
    (left right :
      Var (ids.map fun wire => (diagram.wires wire).sig) sig)
    (same :
      ConcreteElaboration.WireContext.origin diagram ids left =
        ConcreteElaboration.WireContext.origin diagram ids right) :
    left = right := by
  induction ids with
  | nil => nomatch left
  | cons head tail induction =>
      rw [List.nodup_cons] at nodup
      cases left with
      | here =>
          cases right with
          | here => rfl
          | there right =>
              exact False.elim
                (nodup.1 (by
                  change head =
                    ConcreteElaboration.WireContext.origin diagram tail
                      right at same
                  simpa only [← same] using
                    (origin_mem diagram tail right)))
      | there left =>
          cases right with
          | here =>
              exact False.elim
                (nodup.1 (by
                  change
                    ConcreteElaboration.WireContext.origin diagram tail
                        left =
                      head at same
                  simpa only [same] using
                    (origin_mem diagram tail left)))
          | there right =>
              exact congrArg Var.there (induction nodup.2 left right same)

private theorem packed_eq_of_origin
    (diagram : ConcreteDiagram definitionCount)
    (ids : List diagram.WireId)
    (nodup : ids.Nodup)
    (left right :
      PackedVar (ids.map fun wire => (diagram.wires wire).sig))
    (same :
      (match left with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin diagram ids value) =
      (match right with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin diagram ids value)) :
    left = right := by
  rcases left with ⟨leftSig, left⟩
  rcases right with ⟨rightSig, right⟩
  have signature :
      leftSig = rightSig := by
    have leftTyped :=
      ConcreteElaboration.WireContext.origin_signature diagram ids left
    have rightTyped :=
      ConcreteElaboration.WireContext.origin_signature diagram ids right
    exact leftTyped.symm.trans (congrArg (fun wire =>
      (diagram.wires wire).sig) same |>.trans rightTyped)
  subst rightSig
  exact congrArg
    (fun value => (⟨leftSig, value⟩ : PackedVar _))
    (origin_injective diagram ids nodup left right same)

private def evaluatePacked
    {pre : PreModel}
    (env : Env pre sigs) :
    PackedVar sigs → Sigma pre.Domain
  | ⟨sig, value⟩ => ⟨sig, env sig value⟩

private structure RetargetCarrierBatch
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {direction : IdentityRetargetDirection}
    {attachments : List base.val.WireId}
    (compiled : SiteCompilation base site)
    (entries :
      List (CheckedIdentityRetarget base site direction attachments)) where
  carried : ContextCarriesEqualities compiled.frame.context
  covers :
    ∀ entry ∈ entries,
      entry.evidence.identityRegion ≠ site →
        ∃ carrier :
            FrameIdentityCarrier definitions base.val
              (ConcreteElaboration.WireContext.empty base.val)
              compiled.frame entry.evidence.identitySig
              entry.evidence.sourceWire entry.evidence.targetWire,
          ({ sig := entry.evidence.identitySig
             source := carrier.sourceVar
             target := carrier.targetVar } :
              EqualityGuard compiled.frame.visible.sigs) ∈
            carried.guards

private noncomputable def buildRetargetCarrierBatch
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {direction : IdentityRetargetDirection}
    {attachments : List base.val.WireId}
    (compiled : SiteCompilation base site) :
    (entries :
      List (CheckedIdentityRetarget base site direction attachments)) →
      RetargetCarrierBatch compiled entries
  | [] =>
      { carried :=
          ContextCarriesEqualities.emptyFor compiled.frame.context
        covers := by simp }
  | entry :: tail => by
      let nested := buildRetargetCarrierBatch compiled tail
      by_cases strict : entry.evidence.identityRegion ≠ site
      · let carrier :=
          Classical.choice
            (SiteCompilation.carries_identity_strict
              compiled entry.evidence strict)
        let single :=
          ContextCarriesEqualities.ofSingle carrier.carrier
        exact
          { carried := single.combine nested.carried
            covers := by
              intro candidate member candidateStrict
              simp only [List.mem_cons] at member
              rcases member with rfl | tailMember
              · refine ⟨carrier, ?_⟩
                apply ContextCarriesEqualities.mem_combine_left
                exact
                  ContextCarriesEqualities.ofSingle_guard
                    carrier.carrier
              · obtain ⟨tailCarrier, tailGuard⟩ :=
                  nested.covers candidate tailMember candidateStrict
                refine ⟨tailCarrier, ?_⟩
                apply ContextCarriesEqualities.mem_combine_right
                exact tailGuard }
      · exact
          { carried := nested.carried
            covers := by
              intro candidate member candidateStrict
              simp only [List.mem_cons] at member
              rcases member with rfl | tailMember
              · exact False.elim (strict candidateStrict)
              · exact nested.covers candidate tailMember candidateStrict }

private theorem site_visible_nodup
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site) :
    compiled.frame.visible.ids.Nodup := by
  have above :
      ConcreteElaboration.ContextAbove base.val
        (ConcreteElaboration.WireContext.empty base.val) base.val.root :=
    ⟨by simp [ConcreteElaboration.WireContext.empty],
      by
        intro wire member
        simp [ConcreteElaboration.WireContext.empty] at member⟩
  exact
    compileRegionFrame?_visible_nodup definitions base.val base.property site
      (base.val.regionCount + 1) base.val.root
      (ConcreteElaboration.WireContext.empty base.val) compiled.frame above
      compiled.frame_generated

private theorem denoteRegion_cast_context
    {definitions : List (List Sig)}
    {source target : List Sig}
    (same : source = target)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre target)
    (body : Region definitions source) :
    denoteRegion pre definitionEnv env (same ▸ body) ↔
      denoteRegion pre definitionEnv
        (fun sig value => env sig (same ▸ value)) body := by
  cases same
  rfl

private theorem cast_trans
    {α : Sort u} {motive : α → Sort v}
    {left middle right : α}
    (leftMiddle : left = middle)
    (middleRight : middle = right)
    (value : motive left) :
    (leftMiddle.trans middleRight) ▸ value =
      middleRight ▸ (leftMiddle ▸ value) := by
  cases leftMiddle
  cases middleRight
  rfl

private theorem cast_symm_cast
    {α : Sort u} {motive : α → Sort v}
    {left right : α}
    (same : left = right)
    (value : motive left) :
    same.symm ▸ (same ▸ value) = value := by
  cases same
  rfl

private theorem origin_transport_context
    (diagram : ConcreteDiagram definitionCount)
    (left right : ConcreteElaboration.WireContext diagram)
    (same : left = right)
    {sig : Sig}
    (value : Var right.sigs sig) :
    ConcreteElaboration.WireContext.origin diagram left.ids
        (congrArg ConcreteElaboration.WireContext.sigs same |>.symm ▸
          value) =
      ConcreteElaboration.WireContext.origin diagram right.ids value := by
  cases same
  rfl

private theorem site_identity_packed_equal
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site)
    (evidence : IdentityRetarget base site)
    (atSite : evidence.identityRegion = site)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre compiled.frame.visible.sigs)
    (siteDenotes :
      denoteRegion pre definitionEnv env compiled.frame.siteBody)
    (sourcePacked targetPacked :
      PackedVar compiled.frame.visible.sigs)
    (sourceOrigin :
      (match sourcePacked with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin base.val
              compiled.frame.visible.ids value) =
        evidence.sourceWire)
    (targetOrigin :
      (match targetPacked with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin base.val
              compiled.frame.visible.ids value) =
        evidence.targetWire) :
    evaluatePacked env sourcePacked =
      evaluatePacked env targetPacked := by
  obtain ⟨outer, fuel, nodes, children, visibleEquality,
      nodesCompiled, _childrenCompiled, bodyEquality⟩ :=
    compiled.site_origin
  have identityMember :
      evidence.identity ∈ base.val.nodesAt site := by
    apply List.mem_filter.mpr
    refine ⟨Data.Finite.mem_allFin evidence.identity, ?_⟩
    rw [evidence.identity_data, atSite]
    simp only [CNode.region, beq_self_eq_true]
  obtain ⟨sourceVar, targetVar, sourceVarOrigin, targetVarOrigin,
      carried⟩ :=
    compileNodes?_carries_identity base.val base.property
      (outer.extend site) (base.val.nodesAt site) evidence.identity
      (by simpa [atSite] using evidence.identity_data)
      identityMember evidence.sourceWire evidence.targetWire
      evidence.source_incident evidence.target_incident nodes nodesCompiled
  let sameSigs :=
    congrArg ConcreteElaboration.WireContext.sigs visibleEquality
  let outerEnv : Env pre (outer.extend site).sigs :=
    fun sig value => env sig (sameSigs.symm ▸ value)
  have siteItems :
      denoteItemSeq pre definitionEnv outerEnv
        (nodes.append children) := by
    have castDenotes :
        denoteRegion pre definitionEnv outerEnv
          (sameSigs ▸ compiled.frame.siteBody) :=
      (denoteRegion_cast_context sameSigs pre definitionEnv
        outerEnv compiled.frame.siteBody).mpr (by
          have back :
              (fun sig value => outerEnv sig (sameSigs ▸ value)) = env := by
            funext sig value
            dsimp only [outerEnv]
            exact congrArg (env sig)
              (cast_symm_cast
                (motive := fun context : List Sig => Var context sig)
                sameSigs value)
          rw [back]
          exact siteDenotes)
    rw [bodyEquality] at castDenotes
    exact castDenotes
  have nodesDenote :
      denoteItemSeq pre definitionEnv outerEnv nodes :=
    (denoteItemSeq_append pre definitionEnv outerEnv nodes children).mp
      siteItems |>.1
  have equalVars :
      outerEnv evidence.identitySig sourceVar =
        outerEnv evidence.identitySig targetVar :=
    carried.values_equal pre definitionEnv outerEnv nodesDenote
  let sourceVisible :
      Var compiled.frame.visible.sigs evidence.identitySig :=
    sameSigs.symm ▸ sourceVar
  let targetVisible :
      Var compiled.frame.visible.sigs evidence.identitySig :=
    sameSigs.symm ▸ targetVar
  have sourceVisibleOrigin :
      ConcreteElaboration.WireContext.origin base.val
          compiled.frame.visible.ids sourceVisible =
        evidence.sourceWire :=
    (origin_transport_context base.val compiled.frame.visible
      (outer.extend site) visibleEquality sourceVar).trans sourceVarOrigin
  have targetVisibleOrigin :
      ConcreteElaboration.WireContext.origin base.val
          compiled.frame.visible.ids targetVisible =
        evidence.targetWire :=
    (origin_transport_context base.val compiled.frame.visible
      (outer.extend site) visibleEquality targetVar).trans targetVarOrigin
  have equalVisible :
      env evidence.identitySig sourceVisible =
        env evidence.identitySig targetVisible := by
    simpa [outerEnv, sourceVisible, targetVisible] using equalVars
  have nodup := site_visible_nodup compiled
  have sourcePackedExact :
      sourcePacked =
        (⟨evidence.identitySig, sourceVisible⟩ :
          PackedVar compiled.frame.visible.sigs) := by
    apply packed_eq_of_origin base.val compiled.frame.visible.ids nodup
    exact sourceOrigin.trans sourceVisibleOrigin.symm
  have targetPackedExact :
      targetPacked =
        (⟨evidence.identitySig, targetVisible⟩ :
          PackedVar compiled.frame.visible.sigs) := by
    apply packed_eq_of_origin base.val compiled.frame.visible.ids nodup
    exact targetOrigin.trans targetVisibleOrigin.symm
  rw [sourcePackedExact, targetPackedExact]
  exact congrArg (fun value =>
    (⟨evidence.identitySig, value⟩ : Sigma pre.Domain)) equalVisible

private theorem site_identity_retarget_packed_equal
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    (compiled : SiteCompilation base site)
    (evidence : IdentityRetarget base site)
    (direction : IdentityRetargetDirection)
    (atSite : evidence.identityRegion = site)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions)
    (env : Env pre compiled.frame.visible.sigs)
    (siteDenotes :
      denoteRegion pre definitionEnv env compiled.frame.siteBody)
    (expectedPacked replacementPacked :
      PackedVar compiled.frame.visible.sigs)
    (expectedOrigin :
      (match expectedPacked with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin base.val
              compiled.frame.visible.ids value) =
        evidence.expected direction)
    (replacementOrigin :
      (match replacementPacked with
        | ⟨_, value⟩ =>
            ConcreteElaboration.WireContext.origin base.val
              compiled.frame.visible.ids value) =
        evidence.replacement direction) :
    evaluatePacked env replacementPacked =
      evaluatePacked env expectedPacked := by
  cases direction with
  | iteration =>
      exact
        (site_identity_packed_equal compiled evidence atSite pre
          definitionEnv env siteDenotes expectedPacked replacementPacked
          expectedOrigin replacementOrigin).symm
  | deiteration =>
      exact
        site_identity_packed_equal compiled evidence atSite pre
          definitionEnv env siteDenotes replacementPacked expectedPacked
          replacementOrigin expectedOrigin

private def FrameIdentityCarrier.expectedVar
    (carrier :
      FrameIdentityCarrier definitions diagram outer frame sig source target)
    (direction : IdentityRetargetDirection) :
    Var frame.visible.sigs sig :=
  match direction with
  | .iteration => carrier.sourceVar
  | .deiteration => carrier.targetVar

private def FrameIdentityCarrier.replacementVar
    (carrier :
      FrameIdentityCarrier definitions diagram outer frame sig source target)
    (direction : IdentityRetargetDirection) :
    Var frame.visible.sigs sig :=
  match direction with
  | .iteration => carrier.targetVar
  | .deiteration => carrier.sourceVar

private theorem FrameIdentityCarrier.expected_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {evidence : IdentityRetarget base site}
    {outer : ConcreteElaboration.WireContext base.val}
    {frame : RegionFrame definitions base.val outer}
    (carrier :
      FrameIdentityCarrier definitions base.val outer frame
        evidence.identitySig evidence.sourceWire evidence.targetWire)
    (direction : IdentityRetargetDirection) :
    ConcreteElaboration.WireContext.origin base.val frame.visible.ids
        (carrier.expectedVar direction) =
      evidence.expected direction := by
  cases direction with
  | iteration => exact carrier.source_origin
  | deiteration => exact carrier.target_origin

private theorem FrameIdentityCarrier.replacement_origin
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {evidence : IdentityRetarget base site}
    {outer : ConcreteElaboration.WireContext base.val}
    {frame : RegionFrame definitions base.val outer}
    (carrier :
      FrameIdentityCarrier definitions base.val outer frame
        evidence.identitySig evidence.sourceWire evidence.targetWire)
    (direction : IdentityRetargetDirection) :
    ConcreteElaboration.WireContext.origin base.val frame.visible.ids
        (carrier.replacementVar direction) =
      evidence.replacement direction := by
  cases direction with
  | iteration => exact carrier.target_origin
  | deiteration => exact carrier.source_origin

private theorem FrameIdentityCarrier.replacement_value_eq_expected
    (carrier :
      FrameIdentityCarrier definitions diagram outer frame sig source target)
    (direction : IdentityRetargetDirection)
    (env : Env pre frame.visible.sigs)
    (equal :
      env sig carrier.sourceVar = env sig carrier.targetVar) :
    env sig (carrier.replacementVar direction) =
      env sig (carrier.expectedVar direction) := by
  cases direction
  · exact equal.symm
  · exact equal

private theorem Vars.denote_eq_of_entries
    (left : Env pre source)
    (right : Env pre target)
    (sources : Vars source args)
    (targets : Vars target args)
    (entriesEqual :
      ∀ position : Fin args.length,
        evaluatePacked left
            (sources.entries.get
              ⟨position.val, by
                simpa only [ExtractedBoundaryCompiler.entries_length]
                  using position.isLt⟩) =
          evaluatePacked right
            (targets.entries.get
              ⟨position.val, by
                simpa only [ExtractedBoundaryCompiler.entries_length]
                  using position.isLt⟩)) :
    Vars.denote left sources = Vars.denote right targets := by
  induction sources with
  | nil =>
      cases targets
      rfl
  | @cons sig tailArgs source sourceTail induction =>
      cases targets with
      | cons target targetTail =>
          have headEqual := entriesEqual ⟨0, by simp⟩
          simp only [Vars.entries, List.get_eq_getElem,
            List.getElem_cons_zero] at headEqual
          have tailEntriesEqual :
              ∀ position : Fin tailArgs.length,
                evaluatePacked left
                    (sourceTail.entries.get
                      ⟨position.val, by
                        simpa only [
                          ExtractedBoundaryCompiler.entries_length]
                          using position.isLt⟩) =
                  evaluatePacked right
                    (targetTail.entries.get
                      ⟨position.val, by
                        simpa only [
                          ExtractedBoundaryCompiler.entries_length]
                          using position.isLt⟩) := by
            intro position
            have atSuccessor :=
              entriesEqual
                ⟨position.val + 1, by
                  simp only [List.length_cons]
                  omega⟩
            simpa only [Vars.entries, List.get_eq_getElem,
              List.getElem_cons_succ] using atSuccessor
          have tailEqual := induction targetTail tailEntriesEqual
          simp only [Vars.denote_cons]
          apply Prod.ext
          · exact eq_of_heq (Sigma.mk.inj headEqual).2
          · exact tailEqual

private theorem compiled_retarget_equiv
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    {fragmentCompiled : OpenCompilation fragment}
    {direction : IdentityRetargetDirection}
    (checked :
      CheckedIdentityRetargetedSplice base site fragment direction)
    (sourceCompiled :
      InsertionCompilation fragmentCompiled checked.source)
    (targetCompiled :
      InsertionCompilation fragmentCompiled checked.target)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteRegion pre definitionEnv Env.empty targetCompiled.inserted ↔
      denoteRegion pre definitionEnv Env.empty sourceCompiled.inserted := by
  rw [targetCompiled.inserted_eq_insertedAt sourceCompiled.site,
    sourceCompiled.inserted_eq_insertedAt sourceCompiled.site]
  let batch :=
    buildRetargetCarrierBatch sourceCompiled.site
      checked.retargets.entries
  apply batch.carried.equivalence pre definitionEnv
  · intro env guardsEqual
    simp only [Region.denote_conjoin]
    have positionsEqual
        (siteDenotes :
          denoteRegion pre definitionEnv env
            sourceCompiled.site.frame.siteBody) :
        Vars.denote env
            (targetCompiled.positionsAt sourceCompiled.site) =
          Vars.denote env
            (sourceCompiled.positionsAt sourceCompiled.site) := by
        apply Vars.denote_eq_of_entries
        intro position
        let concretePosition : Fin fragment.val.boundary.length :=
          ⟨position.val, by
            simpa only [checkedBoundarySigs, List.length_map] using
              position.isLt⟩
        change
          evaluatePacked env
              (targetCompiled.targetPackedAtAt sourceCompiled.site
                concretePosition) =
            evaluatePacked env
              (sourceCompiled.targetPackedAtAt sourceCompiled.site
                concretePosition)
        rcases checked.target_eq_source_or_entry concretePosition with
          unchanged | changed
        · apply congrArg (evaluatePacked env)
          apply packed_eq_of_origin base.val
            sourceCompiled.site.frame.visible.ids
            (site_visible_nodup sourceCompiled.site)
          exact
            (targetCompiled.targetPackedAtAt_origin sourceCompiled.site
              concretePosition).trans
              (unchanged.trans
                (sourceCompiled.targetPackedAtAt_origin sourceCompiled.site
                  concretePosition).symm)
        · rcases changed with
            ⟨entry, member, atPosition, sourceAt, targetAt⟩
          by_cases atSite :
              entry.evidence.identityRegion = site
          · exact
              site_identity_retarget_packed_equal sourceCompiled.site
                entry.evidence direction atSite pre definitionEnv env
                siteDenotes
                (sourceCompiled.targetPackedAtAt sourceCompiled.site
                  concretePosition)
                (targetCompiled.targetPackedAtAt sourceCompiled.site
                  concretePosition)
                ((sourceCompiled.targetPackedAtAt_origin
                  sourceCompiled.site concretePosition).trans sourceAt)
                ((targetCompiled.targetPackedAtAt_origin
                  sourceCompiled.site concretePosition).trans targetAt)
          · obtain ⟨carrier, guardMember⟩ :=
              batch.covers entry member atSite
            have carriedEqual :=
              guardsEqual
                ({ sig := entry.evidence.identitySig
                   source := carrier.sourceVar
                   target := carrier.targetVar } :
                  EqualityGuard sourceCompiled.site.frame.visible.sigs)
                guardMember
            have sourceExact :
                sourceCompiled.targetPackedAtAt sourceCompiled.site
                    concretePosition =
                  (⟨entry.evidence.identitySig,
                    carrier.expectedVar direction⟩ :
                    PackedVar sourceCompiled.site.frame.visible.sigs) := by
              apply packed_eq_of_origin base.val
                sourceCompiled.site.frame.visible.ids
                (site_visible_nodup sourceCompiled.site)
              exact
                (sourceCompiled.targetPackedAtAt_origin sourceCompiled.site
                  concretePosition).trans
                  (sourceAt.trans
                    (carrier.expected_origin direction).symm)
            have targetExact :
                targetCompiled.targetPackedAtAt sourceCompiled.site
                    concretePosition =
                  (⟨entry.evidence.identitySig,
                    carrier.replacementVar direction⟩ :
                    PackedVar sourceCompiled.site.frame.visible.sigs) := by
              apply packed_eq_of_origin base.val
                sourceCompiled.site.frame.visible.ids
                (site_visible_nodup sourceCompiled.site)
              exact
                (targetCompiled.targetPackedAtAt_origin sourceCompiled.site
                  concretePosition).trans
                  (targetAt.trans
                    (carrier.replacement_origin direction).symm)
            rw [sourceExact, targetExact]
            exact congrArg (fun value =>
              (⟨entry.evidence.identitySig, value⟩ :
                Sigma pre.Domain))
              (carrier.replacement_value_eq_expected direction env
                carriedEqual)
    constructor
    · rintro ⟨siteDenotes, targetDenotes⟩
      refine ⟨siteDenotes, ?_⟩
      rw [denote_intrinsicSplice] at targetDenotes ⊢
      change
        denoteOpen pre definitionEnv fragmentCompiled.openDiagram
          (Vars.denote env
            (targetCompiled.positionsAt sourceCompiled.site))
        at targetDenotes
      change
        denoteOpen pre definitionEnv fragmentCompiled.openDiagram
          (Vars.denote env
            (sourceCompiled.positionsAt sourceCompiled.site))
      rw [positionsEqual siteDenotes] at targetDenotes
      exact targetDenotes
    · rintro ⟨siteDenotes, sourceDenotes⟩
      refine ⟨siteDenotes, ?_⟩
      rw [denote_intrinsicSplice] at sourceDenotes ⊢
      change
        denoteOpen pre definitionEnv fragmentCompiled.openDiagram
          (Vars.denote env
            (sourceCompiled.positionsAt sourceCompiled.site))
        at sourceDenotes
      change
        denoteOpen pre definitionEnv fragmentCompiled.openDiagram
          (Vars.denote env
            (targetCompiled.positionsAt sourceCompiled.site))
      rw [← positionsEqual siteDenotes] at sourceDenotes
      exact sourceDenotes

end IdentityRetargetProof

/--
Two independently accepted generic splices related only by checked,
dominating identity retargets have the same denotation in every premodel.
Both insertion compilations are derived internally from the public splice
equations; callers supply no semantic premise.
-/
theorem identity_retarget_sound
    {definitions : List (List Sig)}
    {base : CheckedDiagram definitions}
    {site : base.val.RegionId}
    {fragment : CheckedOpenDiagram definitions}
    (fragmentCompiled : OpenCompilation fragment)
    {direction : IdentityRetargetDirection}
    (checked :
      CheckedIdentityRetargetedSplice base site fragment direction)
    (sourceResult : ConcreteSpliceResult checked.source)
    (sourceAccepted : splice checked.source = .ok sourceResult)
    (targetResult : ConcreteSpliceResult checked.target)
    (targetAccepted : splice checked.target = .ok targetResult)
    (pre : PreModel.{u})
    (definitionEnv : DefinitionEnv pre definitions) :
    denoteChecked pre definitionEnv targetResult.checked ↔
      denoteChecked pre definitionEnv sourceResult.checked := by
  obtain ⟨sourceCompiled, _sourceGenerated, sourceDenotation⟩ :=
    denote_splice fragmentCompiled checked.source sourceResult
      sourceAccepted pre definitionEnv
  obtain ⟨targetCompiled, _targetGenerated, targetDenotation⟩ :=
    denote_splice fragmentCompiled checked.target targetResult
      targetAccepted pre definitionEnv
  exact targetDenotation.trans
    ((IdentityRetargetProof.compiled_retarget_equiv checked
      sourceCompiled targetCompiled pre definitionEnv).trans
        sourceDenotation.symm)

end VisualProof
