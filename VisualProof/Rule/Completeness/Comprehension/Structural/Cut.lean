import VisualProof.Rule.Completeness.Comprehension.Structural.Hosted
import VisualProof.Rule.Completeness.Comprehension.Structural.Parallel
import VisualProof.Rule.Completeness.Comprehension.Structural.Support

namespace VisualProof.Rule.Completeness.Comprehension

open Diagram
open Theory

namespace Structural

open WirePrimitive

def cutDoubleRenaming (rename : WireRenaming wires target) :
    WireRenaming (wires ++ wires) target :=
  ⟨Var.appendMap (fun wire => rename wire) (fun wire => rename wire)⟩

theorem cutAllPinsAppend
    (first second : List Sig)
    (firstRename : WireRenaming first target)
    (secondRename : WireRenaming second target) :
    EqualityNormalization.allPins (first ++ second)
        ⟨Var.appendMap (fun wire => firstRename wire)
          (fun wire => secondRename wire)⟩ =
      (EqualityNormalization.allPins first firstRename).append
        (EqualityNormalization.allPins second secondRename) := by
  induction first with
  | nil => rfl
  | cons signature rest induction =>
      let tailRename : WireRenaming rest target :=
        ⟨fun wire => firstRename (.there wire)⟩
      change ItemSeq.cons
          (.identity signature 1 (fun _ => firstRename .here))
          (EqualityNormalization.allPins (rest ++ second)
            ⟨Var.appendMap (fun wire => tailRename wire)
              (fun wire => secondRename wire)⟩) =
        ItemSeq.cons (.identity signature 1 (fun _ => firstRename .here))
          ((EqualityNormalization.allPins rest tailRename).append
            (EqualityNormalization.allPins second secondRename))
      congr 1
      exact induction tailRename

theorem cutAllPinsDouble
    (wires : List Sig) (rename : WireRenaming wires target) :
    EqualityNormalization.allPins (wires ++ wires)
        (cutDoubleRenaming rename) =
      (EqualityNormalization.allPins wires rename).append
        (EqualityNormalization.allPins wires rename) := by
  exact cutAllPinsAppend wires wires rename rename

theorem cutDoubleRenaming_comp
    (first : WireRenaming source middle)
    (second : WireRenaming middle target) :
    WireRenaming.comp second (cutDoubleRenaming first) =
      cutDoubleRenaming (WireRenaming.comp second first) := by
  apply WireRenaming.ext
  intro signature wire
  apply Var.appendCases (left := source) (right := source)
    (motive := fun wire =>
      WireRenaming.comp second (cutDoubleRenaming first) wire =
        cutDoubleRenaming (WireRenaming.comp second first) wire)
  · intro signature left
    simp [WireRenaming.comp, cutDoubleRenaming]
  · intro signature right
    simp [WireRenaming.comp, cutDoubleRenaming]

mutual
  /-- Deterministic support for every local home crossed by CutShape. -/
  def cutSupportedRegion : {wires : List Sig} → Region wires → Region wires
    | wires, .mk locals items =>
        .mk locals ((cutSupportedItems items).append
          (EqualityNormalization.allPins (locals ++ locals)
            (cutDoubleRenaming
              ⟨fun wire => Var.appendRight wires wire⟩)))

  def cutSupportedItem : {wires : List Sig} → Item wires → Item wires
    | _, .atom head ports => .atom head ports
    | _, .identity signature arity ports =>
        .identity signature arity ports
    | _, .cut body => .cut (cutSupportedRegion body)

  def cutSupportedItems : {wires : List Sig} →
      ItemSeq wires → ItemSeq wires
    | _, .nil => .nil
    | _, .cons head tail =>
        .cons (cutSupportedItem head) (cutSupportedItems tail)
end

def cutSupportedRootItems
  (pinWires : List Sig) (pinRename : WireRenaming pinWires wires)
    (items : ItemSeq wires) : ItemSeq wires :=
  (cutSupportedItems items).append
    (EqualityNormalization.allPins (pinWires ++ pinWires)
      (cutDoubleRenaming pinRename))

theorem cutAppendLocalPinsScope
    (locals : List Sig) (items : ItemSeq (outer ++ locals)) :
    ScopePreservation (.mk locals items : Region outer)
      (.mk locals (items.append
        (EqualityNormalization.allPins (locals ++ locals)
          (cutDoubleRenaming
            ⟨fun wire => Var.appendRight outer wire⟩)))) := by
  let rename : WireRenaming locals (outer ++ locals) :=
    ⟨fun wire => Var.appendRight outer wire⟩
  let pins := EqualityNormalization.allPins locals rename
  have pinsEq : EqualityNormalization.allPins (locals ++ locals)
      (cutDoubleRenaming rename) = pins.append pins :=
    cutAllPinsDouble locals rename
  rw [pinsEq]
  have pinsEmpty {signature : Sig} (wire : Var outer signature)
      (itemIndex : Nat) :
      (pins.append pins).incidencePaths wire.index.val itemIndex = [] := by
    rw [ItemSeq.incidencePaths_append]
    have once : pins.incidencePaths wire.index.val itemIndex = [] := by
      apply ItemSeq.pinWires_incidence_eq_nil_of
      intro localSignature localWire _
      dsimp only [rename]
      have wireBound := wire.index.isLt
      simp only [Var.index_appendRight]
      omega
    have twice : pins.incidencePaths wire.index.val
        (itemIndex + pins.length) = [] := by
      apply ItemSeq.pinWires_incidence_eq_nil_of
      intro localSignature localWire _
      dsimp only [rename]
      have wireBound := wire.index.isLt
      simp only [Var.index_appendRight]
      omega
    rw [once, twice]
    rfl
  constructor
  · intro sourceCanonical
    constructor
    · intro localIndex
      let localWire : Var (outer ++ locals) (locals.get localIndex) :=
        Var.appendRight outer (Var.ofIndex localIndex)
      have rooted := EqualityNormalization.allPins_twice_rooted
        locals rename (Var.ofIndex localIndex) items.length
      rw [ItemSeq.incidencePaths_append]
      apply RegionPath.RootedTwo.of_sublist
        (List.sublist_append_right _ _)
      simpa [localWire, rename] using rooted
    · exact (ItemSeq.childrenCanonical_append _ _).mpr
        ⟨sourceCanonical.2,
          EqualityNormalization.allPins_twice_childrenCanonical
            locals rename⟩
  · intro signature wire
    simp only [Region.incidencePaths]
    rw [ItemSeq.incidencePaths_append, pinsEmpty, List.append_nil]
  · intro signature wire rooted
    simp only [Region.incidencePaths]
    rw [ItemSeq.incidencePaths_append, pinsEmpty, List.append_nil]
    simpa only [Region.incidencePaths] using rooted

theorem cutSupportedRegionHostedCase
    (locals : List Sig) (items : ItemSeq (wires ++ locals))
    (itemsBridge : HostedStrict (Region.ofItems items)
      (Region.ofItems (cutSupportedItems items))) :
    HostedStrict (.mk locals items : Region wires)
      (cutSupportedRegion (.mk locals items : Region wires)) := by
  let pinsRename : WireRenaming locals (wires ++ locals) :=
    ⟨fun wire => Var.appendRight wires wire⟩
  let pins := EqualityNormalization.allPins (locals ++ locals)
    (cutDoubleRenaming pinsRename)
  let combined := HostedStrict.conjoin
    (Region.ofItems items) (Region.blank (wires ++ locals))
    (Region.ofItems (cutSupportedItems items))
    (Region.ofItems pins) itemsBridge
    (HostedStrict.iso (RegionIso.refl _)
      (RegionIso.ofEq (congrArg Region.ofItems
        (cutAllPinsDouble locals pinsRename).symm))
      (HostedStrict.allPinsTwice locals pinsRename))
  let lifted := HostedStrict.adjoinAt locals _ _ combined
  apply HostedStrict.iso
    ((RegionIso.adjoinAtOfItems locals items).symm.trans
      (RegionIso.adjoinAt locals .nil
        (RegionIso.conjoinBlank (Region.ofItems items)).symm))
    ((RegionIso.adjoinAt locals .nil
      (RegionIso.ofEq (Region.ofItems_conjoin
        (cutSupportedItems items) pins))).trans
      (RegionIso.adjoinAtOfItems locals
        ((cutSupportedItems items).append pins)))
    lifted

theorem cutSupportedAtomHosted
    (head : Var wires (.rel arguments)) (ports : Vars wires arguments) :
    HostedStrict (Region.singleton (.atom head ports))
      (Region.singleton (cutSupportedItem (.atom head ports))) := by
  exact HostedStrict.refl _

theorem cutSupportedIdentityHosted
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) :
    HostedStrict (Region.singleton (.identity signature arity ports))
      (Region.singleton (cutSupportedItem
        (.identity signature arity ports))) := by
  exact HostedStrict.refl _

theorem cutSupportedCutHosted (body : Region wires)
    (bodyBridge : HostedStrict body (cutSupportedRegion body)) :
    HostedStrict (Region.singleton (.cut body))
      (Region.singleton (cutSupportedItem (.cut body))) := by
  exact HostedStrict.cut body (cutSupportedRegion body) bodyBridge

theorem cutSupportedNilHosted {wires : List Sig} :
    HostedStrict (Region.ofItems (.nil : ItemSeq wires))
      (Region.ofItems (cutSupportedItems (.nil : ItemSeq wires))) := by
  exact HostedStrict.refl _

theorem cutSupportedConsHosted
    (head : Item wires) (tail : ItemSeq wires)
    (headBridge : HostedStrict (Region.singleton head)
      (Region.singleton (cutSupportedItem head)))
    (tailBridge : HostedStrict (Region.ofItems tail)
      (Region.ofItems (cutSupportedItems tail))) :
    HostedStrict (Region.ofItems (.cons head tail))
      (Region.ofItems (cutSupportedItems (.cons head tail))) := by
  apply HostedStrict.iso
    (RegionIso.ofEq (Region.singleton_conjoin_ofItems head tail)).symm
    (RegionIso.ofEq (Region.singleton_conjoin_ofItems
      (cutSupportedItem head) (cutSupportedItems tail)))
  exact HostedStrict.conjoin _ _ _ _ headBridge tailBridge

theorem cutSupportedItemsHosted (items : ItemSeq wires) :
    HostedStrict (Region.ofItems items)
      (Region.ofItems (cutSupportedItems items)) := by
  exact ItemSeq.rec
    (motive_1 := fun _ region =>
      HostedStrict region (cutSupportedRegion region))
    (motive_2 := fun _ item => HostedStrict (Region.singleton item)
      (Region.singleton (cutSupportedItem item)))
    (motive_3 := fun _ items => HostedStrict (Region.ofItems items)
      (Region.ofItems (cutSupportedItems items)))
    cutSupportedRegionHostedCase cutSupportedAtomHosted
    cutSupportedIdentityHosted cutSupportedCutHosted
    (@cutSupportedNilHosted) cutSupportedConsHosted items

theorem cutSupportedRootItemsHosted
    (pinWires : List Sig) (pinRename : WireRenaming pinWires wires)
    (items : ItemSeq wires) :
    HostedStrict (Region.ofItems items)
      (Region.ofItems (cutSupportedRootItems pinWires pinRename items)) := by
  let combined := HostedStrict.conjoin
    (Region.ofItems items) (Region.blank wires)
    (Region.ofItems (cutSupportedItems items))
    (Region.ofItems (EqualityNormalization.allPins
      (pinWires ++ pinWires) (cutDoubleRenaming pinRename)))
    (cutSupportedItemsHosted items)
    (HostedStrict.iso (RegionIso.refl _)
      (RegionIso.ofEq (congrArg Region.ofItems
        (cutAllPinsDouble pinWires pinRename).symm))
      (HostedStrict.allPinsTwice pinWires pinRename))
  apply HostedStrict.iso (RegionIso.conjoinBlank _).symm
    (RegionIso.ofEq ?_) combined
  simp only [cutSupportedRootItems]
  exact Region.ofItems_conjoin _ _

theorem cutSupportedRegionScopeCase
    (locals : List Sig) (items : ItemSeq (wires ++ locals))
    (itemsScope : ScopePreservation (Region.ofItems items)
      (Region.ofItems (cutSupportedItems items))) :
    ScopePreservation (.mk locals items : Region wires)
      (cutSupportedRegion (.mk locals items : Region wires)) := by
  have sourcePresentation := ScopePreservation.ofIso
    (RegionIso.adjoinAtOfItems locals items).symm
  have lifted := adjoinAt_preserves_scope locals .nil
    (Region.ofItems items) (Region.ofItems (cutSupportedItems items))
    itemsScope
  have targetPresentation := ScopePreservation.ofIso
    (RegionIso.adjoinAtOfItems locals (cutSupportedItems items))
  have supportedItemsScope := sourcePresentation.trans
    (lifted.trans targetPresentation)
  exact supportedItemsScope.trans
    (cutAppendLocalPinsScope locals (cutSupportedItems items))

theorem cutSupportedAtomScope
    (head : Var wires (.rel arguments)) (ports : Vars wires arguments) :
    ScopePreservation (Region.singleton (.atom head ports))
      (Region.singleton (cutSupportedItem (.atom head ports))) := by
  exact ScopePreservation.refl _

theorem cutSupportedIdentityScope
    (signature : Sig) (arity : Nat)
    (ports : Fin arity → Var wires signature) :
    ScopePreservation (Region.singleton (.identity signature arity ports))
      (Region.singleton (cutSupportedItem
        (.identity signature arity ports))) := by
  exact ScopePreservation.refl _

theorem cutSupportedCutScope (body : Region wires)
    (bodyScope : ScopePreservation body (cutSupportedRegion body)) :
    ScopePreservation (Region.singleton (.cut body))
      (Region.singleton (cutSupportedItem (.cut body))) := by
  exact ScopePreservation.cut bodyScope

theorem cutSupportedNilScope {wires : List Sig} :
    ScopePreservation (Region.ofItems (.nil : ItemSeq wires))
      (Region.ofItems (cutSupportedItems (.nil : ItemSeq wires))) := by
  exact ScopePreservation.refl _

theorem cutSupportedConsScope
    (head : Item wires) (tail : ItemSeq wires)
    (headScope : ScopePreservation (Region.singleton head)
      (Region.singleton (cutSupportedItem head)))
    (tailScope : ScopePreservation (Region.ofItems tail)
      (Region.ofItems (cutSupportedItems tail))) :
    ScopePreservation (Region.ofItems (.cons head tail))
      (Region.ofItems (cutSupportedItems (.cons head tail))) := by
  exact (ScopePreservation.ofIso
      (RegionIso.ofEq (Region.singleton_conjoin_ofItems head tail)).symm).trans
    ((ScopePreservation.conjoin headScope tailScope).trans
      (ScopePreservation.ofIso (RegionIso.ofEq
        (Region.singleton_conjoin_ofItems
          (cutSupportedItem head) (cutSupportedItems tail)))))

theorem cutSupportedItemsScope (items : ItemSeq wires) :
    ScopePreservation (Region.ofItems items)
      (Region.ofItems (cutSupportedItems items)) := by
  exact ItemSeq.rec
    (motive_1 := fun _ region =>
      ScopePreservation region (cutSupportedRegion region))
    (motive_2 := fun _ item => ScopePreservation (Region.singleton item)
      (Region.singleton (cutSupportedItem item)))
    (motive_3 := fun _ items => ScopePreservation (Region.ofItems items)
      (Region.ofItems (cutSupportedItems items)))
    cutSupportedRegionScopeCase cutSupportedAtomScope
    cutSupportedIdentityScope cutSupportedCutScope
    (@cutSupportedNilScope) cutSupportedConsScope items

/-- Prepend one deterministic retained-pin batch to an existing Cut edit and
recursive instantiation witness. -/
theorem cutPrependPinsFactor
    {arguments common actualWires pinWires : List Sig}
    (childPattern : OpenDiagram arguments)
    {frame : Transform.Frame arguments common actualWires actualWires}
    (data : (Content.Cut.operation arguments).Data frame)
    (invariant : Transform.IndexedHeadInvariant frame data)
    (pinCommon : WireRenaming pinWires common)
    {tailSource : ItemSeq actualWires}
    (tailEdit : Transform.ItemsEdit (Content.Cut.operation arguments)
      frame data tailSource)
    {tailTarget : ItemSeq actualWires} {tailResult : Region common}
    (tailEvidence :
      VisualProof.Rule.Comprehension.Instantiation.ItemsResult
        childPattern frame.targetKeep data tailTarget tailResult)
    (tailIso : Nonempty (RegionIso (WireEquiv.refl actualWires)
      tailEdit.run (Region.ofItems tailTarget)))
    (tailCanonical : (Region.ofItems tailSource).Canonical →
      tailEdit.run.Canonical)
    (tailRetained : ∀ {signature} (wire : Var common signature),
      SupportParallelIncidenceScope
        ((Region.ofItems tailSource).incidencePaths
          (frame.sourceKeep wire).index.val)
        (tailEdit.run.incidencePaths (frame.targetKeep wire).index.val))
    (tailSelected : SupportParallelIncidenceScope
      ((Region.ofItems tailSource).incidencePaths frame.selected.index.val)
      (tailEdit.run.incidencePaths data.index.val)) :
    ∃ edit : Transform.ItemsEdit (Content.Cut.operation arguments)
        frame data
        ((EqualityNormalization.allPins pinWires
          (WireRenaming.comp frame.sourceKeep pinCommon)).append tailSource),
      ∃ target : ItemSeq actualWires,
        ∃ result : Region common,
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult
              childPattern frame.targetKeep data target result ∧
            Nonempty (RegionIso (WireEquiv.refl actualWires)
              edit.run (Region.ofItems target)) ∧
            HostedStrict tailResult result ∧
            Nonempty (RegionIso (WireEquiv.refl common)
              ((Region.ofItems (EqualityNormalization.allPins pinWires
                pinCommon)).conjoin
                  tailResult) result) ∧
            ((Region.ofItems
                ((EqualityNormalization.allPins pinWires
                  (WireRenaming.comp frame.sourceKeep pinCommon)).append
                    tailSource)).Canonical → edit.run.Canonical) ∧
            (∀ {signature} (wire : Var common signature),
              SupportParallelIncidenceScope
                ((Region.ofItems
                  ((EqualityNormalization.allPins pinWires
                    (WireRenaming.comp frame.sourceKeep pinCommon)).append
                      tailSource)).incidencePaths
                        (frame.sourceKeep wire).index.val)
                (edit.run.incidencePaths
                  (frame.targetKeep wire).index.val)) ∧
            SupportParallelIncidenceScope
              ((Region.ofItems
                ((EqualityNormalization.allPins pinWires
                  (WireRenaming.comp frame.sourceKeep pinCommon)).append
                    tailSource)).incidencePaths frame.selected.index.val)
              (edit.run.incidencePaths data.index.val) := by
  induction pinWires with
  | nil =>
      exact ⟨tailEdit, tailTarget, tailResult, tailEvidence, tailIso,
        HostedStrict.refl _, ⟨RegionIso.blankConjoin tailResult⟩,
        tailCanonical, tailRetained, tailSelected⟩
  | cons signature rest induction =>
      let tailCommon : WireRenaming rest common :=
        ⟨fun wire => pinCommon (.there wire)⟩
      obtain ⟨restEdit, restTarget, restResult, restEvidence,
          ⟨restIso⟩, restBridge, ⟨restPresentation⟩,
          restCanonical, restRetained, restSelected⟩ :=
        induction tailCommon
      let commonWire : Var common signature := pinCommon .here
      let sourcePin : Item actualWires :=
        .identity signature 1 (fun _ => frame.sourceKeep commonWire)
      let targetPin : Item actualWires :=
        .identity signature 1 (fun _ => frame.targetKeep commonWire)
      let prependedResult : Region common :=
        Region.singleton (.identity signature 1 (fun _ => commonWire))
      let pinEdit : Transform.ItemEdit (Content.Cut.operation arguments)
          frame data sourcePin :=
        .identity signature 1 (fun _ => commonWire)
      let pinEvidence :=
        VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
          (pattern := childPattern) (retain := frame.targetKeep)
          (selected := data) signature 1 (fun _ => commonWire)
      let edit := Transform.ItemsEdit.cons pinEdit restEdit
      let target := ItemSeq.cons targetPin restTarget
      let result := prependedResult.conjoin restResult
      have editIso : Nonempty (RegionIso (WireEquiv.refl actualWires)
          edit.run (Region.ofItems target)) := by
        let combined := RegionIso.conjoinCongr
          (RegionIso.refl (Region.singleton targetPin)) restIso
        exact ⟨combined.trans (RegionIso.ofEq
          (Region.singleton_conjoin_ofItems targetPin restTarget))⟩
      let pinRename : WireRenaming [signature] common :=
        ⟨fun wire => by
          cases wire with
          | here => exact commonWire
          | there impossible => exact Fin.elim0 impossible.index⟩
      let pinBridge := HostedStrict.specialize
        (HostedStrict.unaryPin signature) pinRename (by rfl) (by rfl)
      let resultBridge := HostedStrict.iso
        (RegionIso.blankConjoin tailResult).symm (RegionIso.refl result)
        (HostedStrict.conjoin (Region.blank common) tailResult
          prependedResult restResult pinBridge restBridge)
      let pinsTail := EqualityNormalization.allPins rest
        tailCommon
      let sourcePresentation := RegionIso.conjoinCongr
        (RegionIso.ofEq
          (Region.singleton_conjoin_ofItems
            (.identity signature 1 (fun _ => commonWire)) pinsTail).symm)
        (RegionIso.refl tailResult)
      let reassociated := RegionIso.conjoinAssoc prependedResult
        (Region.ofItems pinsTail) tailResult
      let resultPresentation := sourcePresentation.trans
        (reassociated.trans
          (RegionIso.conjoinCongr (RegionIso.refl prependedResult)
            restPresentation))
      have pinEq : sourcePin = targetPin := by
        simp only [sourcePin, targetPin]
        congr 2
        funext index
        apply Var.eq_of_index_eq
        apply Fin.ext
        exact invariant.2.1 commonWire
      have pinRunEq : pinEdit.run = Region.singleton sourcePin := by
        change Region.singleton targetPin = Region.singleton sourcePin
        rw [pinEq]
      have editCanonical :
          (Region.ofItems (.cons sourcePin
            ((EqualityNormalization.allPins rest
              (WireRenaming.comp frame.sourceKeep tailCommon)).append
                tailSource))).Canonical → edit.run.Canonical := by
        intro sourceCanonical
        rw [← Region.singleton_conjoin_ofItems] at sourceCanonical
        have components := (Region.Canonical.conjoin_iff _ _).mp
          sourceCanonical
        change (Region.singleton targetPin).conjoin restEdit.run |>.Canonical
        exact (Region.Canonical.conjoin_iff _ _).mpr
          ⟨pinEq ▸ components.1, restCanonical components.2⟩
      have retainedScope : ∀ {wireSignature}
          (wire : Var common wireSignature),
          SupportParallelIncidenceScope
            ((Region.ofItems (.cons sourcePin
              ((EqualityNormalization.allPins rest
                (WireRenaming.comp frame.sourceKeep tailCommon)).append
                  tailSource))).incidencePaths
                    (frame.sourceKeep wire).index.val)
            (edit.run.incidencePaths (frame.targetKeep wire).index.val) := by
        intro wireSignature wire
        rw [← Region.singleton_conjoin_ofItems]
        exact SupportParallelIncidenceScope.conjoin
          (frame.sourceKeep wire) (frame.targetKeep wire)
          (by
            rw [pinRunEq]
            simpa only [invariant.2.1 wire] using
              (SupportParallelIncidenceScope.refl
                ((Region.singleton sourcePin).incidencePaths
                  (frame.sourceKeep wire).index.val)))
          (restRetained wire)
      have selectedScope : SupportParallelIncidenceScope
          ((Region.ofItems (.cons sourcePin
            ((EqualityNormalization.allPins rest
              (WireRenaming.comp frame.sourceKeep tailCommon)).append
                tailSource))).incidencePaths frame.selected.index.val)
          (edit.run.incidencePaths data.index.val) := by
        rw [← Region.singleton_conjoin_ofItems]
        exact SupportParallelIncidenceScope.conjoin frame.selected data
          (by
            rw [pinRunEq]
            simpa only [invariant.2.2] using
              (SupportParallelIncidenceScope.refl
                ((Region.singleton sourcePin).incidencePaths
                  frame.selected.index.val))) restSelected
      exact ⟨edit, target, result,
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
          pinEvidence restEvidence,
        editIso, resultBridge, ⟨resultPresentation⟩,
        editCanonical, retainedScope, selectedScope⟩

mutual
  theorem cutRegionFactor
      {wires common actualWires : List Sig}
      (body : Region wires) (bodyCanonical : body.Canonical)
      {frame : Transform.Frame wires common actualWires actualWires}
      (data : (Content.Cut.operation wires).Data frame)
      (invariant : Transform.IndexedHeadInvariant frame data)
      (retainedSelected : ∀ {signature} (wire : Var common signature),
        (frame.sourceKeep wire).index.val ≠ frame.selected.index.val)
      {source : Region actualWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.RegionResult
          (Erasure.Exposure.supportPattern (Region.singleton (.cut body))
            ((Region.singleton_cut_canonical_iff body).mpr bodyCanonical))
          frame.sourceKeep frame.selected source result) :
      ∃ edit : Transform.RegionEdit (Content.Cut.operation wires)
          frame data (cutSupportedRegion source),
        ∃ childSource : Region actualWires,
          ∃ childResult : Region common,
            VisualProof.Rule.Comprehension.Instantiation.RegionResult
                (Erasure.Exposure.supportPattern body bodyCanonical)
                frame.targetKeep data childSource childResult ∧
              Nonempty (RegionIso (WireEquiv.refl actualWires)
                edit.run childSource) ∧
              HostedStrict result childResult ∧
              (result.Canonical → childResult.Canonical) ∧
              (∀ {signature} (wire : Var common signature),
                result.incidencePaths wire.index.val ≠ [] ↔
                  childResult.incidencePaths wire.index.val ≠ []) ∧
              ((cutSupportedRegion source).Canonical →
                childSource.Canonical) ∧
              (∀ {signature} (wire : Var common signature),
                (cutSupportedRegion source).incidencePaths
                      (frame.sourceKeep wire).index.val ≠ [] ↔
                  childSource.incidencePaths
                      (frame.targetKeep wire).index.val ≠ []) ∧
              SupportParallelIncidenceScope
                ((cutSupportedRegion source).incidencePaths
                  frame.selected.index.val)
                (childSource.incidencePaths data.index.val) := by
    cases evidence with
    | @mk _ _ _ _ locals items itemResult childEvidence =>
        let childFrame := frame.append locals
        let childData := (Content.Cut.operation wires).appendData
          frame data locals
        let pinCommon : WireRenaming locals (common ++ locals) :=
          ⟨fun wire => Var.appendRight common wire⟩
        obtain ⟨childEdit, childItems, recursiveResult,
            recursiveEvidence, ⟨childIso⟩, childBridge,
            recursiveCanonical, recursiveNonempty, recursiveRooted,
            childSourceCanonical, childSourceNonempty, childSelectedScope,
            childSourceRooted⟩ :=
          cutItemsFactor body bodyCanonical childData
            (invariant.append locals) (by
              intro signature wire
              apply Var.appendCases (left := common) (right := locals)
                (motive := fun wire =>
                  ((frame.append locals).sourceKeep wire).index.val ≠
                    (frame.append locals).selected.index.val)
              · intro inheritedSignature inherited
                simpa [Transform.Frame.append, WireRenaming.appendRight]
                  using retainedSelected inherited
              · intro localSignature localWire
                simp [Transform.Frame.append, WireRenaming.appendRight]
                omega) pinCommon childEvidence
        have sourceEq : cutSupportedRegion (.mk locals items) =
            .mk locals
              (cutSupportedRootItems locals
                (WireRenaming.comp childFrame.sourceKeep pinCommon) items) := by
          simp only [cutSupportedRegion, cutSupportedRootItems, childFrame,
            Transform.Frame.append]
          congr 2
          apply congrArg
          apply congrArg
          apply WireRenaming.ext
          intro signature wire
          simp [pinCommon, WireRenaming.comp, WireRenaming.appendRight]
        rw [sourceEq]
        let edit : Transform.RegionEdit (Content.Cut.operation wires)
            frame data (.mk locals
              (cutSupportedRootItems locals
                (WireRenaming.comp childFrame.sourceKeep pinCommon) items)) :=
          Transform.RegionEdit.mk childEdit
        let childSource : Region actualWires := .mk locals childItems
        let childResult := Region.adjoinAt locals .nil recursiveResult
        have runIso : Nonempty (RegionIso (WireEquiv.refl actualWires)
            edit.run childSource) := by
          have runEq : edit.run =
              Region.adjoinAt locals .nil childEdit.run := by
            rfl
          let lifted := RegionIso.adjoinAt locals .nil childIso
          let presented := (RegionIso.ofEq runEq).trans (lifted.trans
            (RegionIso.adjoinAtOfItems locals childItems))
          exact ⟨presented.castAmbient (WireEquiv.refl_trans _)⟩
        exact ⟨edit, childSource, childResult,
          VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
            recursiveEvidence,
          runIso,
          HostedStrict.adjoinAt locals itemResult recursiveResult
            childBridge,
          (by
            intro sourceCanonical
            have materialCanonical :=
              Region.Canonical.material_of_adjoinAt locals .nil itemResult
                sourceCanonical
            apply Region.Canonical.adjoinAt_of_material_roots locals .nil
              recursiveResult True.intro
              (recursiveCanonical materialCanonical)
            intro localIndex
            let localWire : Var locals (locals.get localIndex) :=
              Var.ofIndex localIndex
            simpa [childResult, pinCommon, localWire] using
              (recursiveRooted localWire)),
          (by
            intro signature wire
            let childWire := wire.appendLeft locals
            have sourcePaths := Region.incidencePaths_adjoinAt_nil itemResult
              childWire
            have targetPaths := Region.incidencePaths_adjoinAt_nil
              recursiveResult childWire
            have inherited := recursiveNonempty childWire (by
              intro pinSignature pin
              simp [childWire, pinCommon]
              omega)
            change
              (Region.adjoinAt locals .nil itemResult).incidencePaths
                    wire.index.val ≠ [] ↔
                (Region.adjoinAt locals .nil recursiveResult).incidencePaths
                    wire.index.val ≠ []
            rw [show wire.index.val = childWire.index.val by
              simp [childWire], sourcePaths, targetPaths]
            exact inherited),
          (by
            intro sourceCanonical
            have sourceAdjoinedCanonical :
                (Region.adjoinAt locals .nil
                  (Region.ofItems
                    (cutSupportedRootItems locals
                      (WireRenaming.comp childFrame.sourceKeep pinCommon)
                        items))).Canonical :=
              (RegionIso.adjoinAtOfItems locals _).canonical_iff.mpr
                sourceCanonical
            have materialCanonical :=
              Region.Canonical.material_of_adjoinAt locals .nil
                (Region.ofItems
                  (cutSupportedRootItems locals
                    (WireRenaming.comp childFrame.sourceKeep pinCommon)
                      items)) sourceAdjoinedCanonical
            apply (RegionIso.adjoinAtOfItems locals childItems).canonical_iff.mp
            apply Region.Canonical.adjoinAt_of_material_roots locals .nil
                (Region.ofItems childItems) True.intro
                (childSourceCanonical materialCanonical)
            intro localIndex
            let localWire : Var locals (locals.get localIndex) :=
              Var.ofIndex localIndex
            have indexEq :
                ((childFrame.targetKeep (pinCommon localWire)).index.val) =
                  actualWires.length + localIndex.val := by
              simp [pinCommon, childFrame, localWire,
                Transform.Frame.append, WireRenaming.appendRight]
            rw [← indexEq]
            exact childSourceRooted localWire),
          (by
            intro signature wire
            let sourceWire := frame.sourceKeep wire
            let targetWire := frame.targetKeep wire
            let childCommonWire := wire.appendLeft locals
            have sourcePaths := Region.incidencePaths_adjoinAt_nil
              (Region.ofItems
                (cutSupportedRootItems locals
                  (WireRenaming.comp childFrame.sourceKeep pinCommon) items))
              (sourceWire.appendLeft locals)
            have targetPaths := Region.incidencePaths_adjoinAt_nil
              (Region.ofItems childItems) (targetWire.appendLeft locals)
            have inherited := childSourceNonempty childCommonWire
            have adjoinedNonempty :
                (Region.adjoinAt locals .nil
                    (Region.ofItems
                      (cutSupportedRootItems locals
                        (WireRenaming.comp childFrame.sourceKeep pinCommon)
                          items))).incidencePaths sourceWire.index.val ≠ [] ↔
                  (Region.adjoinAt locals .nil
                    (Region.ofItems childItems)).incidencePaths
                      targetWire.index.val ≠ [] := by
              rw [show sourceWire.index.val =
                  (sourceWire.appendLeft locals).index.val by simp,
                show targetWire.index.val =
                  (targetWire.appendLeft locals).index.val by simp]
              rw [sourcePaths, targetPaths]
              simpa [childFrame, childCommonWire, sourceWire, targetWire,
                Transform.Frame.append, WireRenaming.appendRight] using inherited
            let sourceIso := RegionIso.adjoinAtOfItems locals
              (cutSupportedRootItems locals
                (WireRenaming.comp childFrame.sourceKeep pinCommon) items)
            let targetIso := RegionIso.adjoinAtOfItems locals childItems
            exact (supportParallelNonemptyOfLengthEq
                (sourceIso.incidencePaths_length_eq sourceWire)).symm.trans
              (adjoinedNonempty.trans
                (supportParallelNonemptyOfLengthEq
                  (targetIso.incidencePaths_length_eq targetWire)))),
          (by
            have sourcePaths := Region.incidencePaths_adjoinAt_nil
              (Region.ofItems
                (cutSupportedRootItems locals
                  (WireRenaming.comp childFrame.sourceKeep pinCommon) items))
              (frame.selected.appendLeft locals)
            have targetPaths := Region.incidencePaths_adjoinAt_nil
              (Region.ofItems childItems) (data.appendLeft locals)
            have adjoinedScope : SupportParallelIncidenceScope
                ((Region.adjoinAt locals .nil
                  (Region.ofItems
                    (cutSupportedRootItems locals
                      (WireRenaming.comp childFrame.sourceKeep pinCommon)
                        items))).incidencePaths frame.selected.index.val)
                ((Region.adjoinAt locals .nil
                  (Region.ofItems childItems)).incidencePaths data.index.val) := by
              rw [show frame.selected.index.val =
                  (frame.selected.appendLeft locals).index.val by simp,
                show data.index.val =
                  (data.appendLeft locals).index.val by simp]
              rw [sourcePaths, targetPaths]
              simpa [childFrame, childData, Transform.Frame.append,
                Content.Cut.operation] using childSelectedScope
            exact SupportParallelIncidenceScope.iso
              (RegionIso.adjoinAtOfItems locals _).symm
              (RegionIso.adjoinAtOfItems locals _) frame.selected data
              adjoinedScope)⟩
  termination_by sizeOf source

  theorem cutItemsFactor
      {wires common actualWires pinWires : List Sig}
      (body : Region wires) (bodyCanonical : body.Canonical)
      {frame : Transform.Frame wires common actualWires actualWires}
      (data : (Content.Cut.operation wires).Data frame)
      (invariant : Transform.IndexedHeadInvariant frame data)
      (retainedSelected : ∀ {signature} (wire : Var common signature),
        (frame.sourceKeep wire).index.val ≠ frame.selected.index.val)
      (pinCommon : WireRenaming pinWires common)
      {source : ItemSeq actualWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemsResult
          (Erasure.Exposure.supportPattern (Region.singleton (.cut body))
            ((Region.singleton_cut_canonical_iff body).mpr bodyCanonical))
          frame.sourceKeep frame.selected source result) :
      ∃ edit : Transform.ItemsEdit (Content.Cut.operation wires)
          frame data
            (cutSupportedRootItems pinWires
              (WireRenaming.comp frame.sourceKeep pinCommon) source),
        ∃ childSource : ItemSeq actualWires,
          ∃ childResult : Region common,
            VisualProof.Rule.Comprehension.Instantiation.ItemsResult
                (Erasure.Exposure.supportPattern body bodyCanonical)
                frame.targetKeep data childSource childResult ∧
              Nonempty (RegionIso (WireEquiv.refl actualWires)
                edit.run (Region.ofItems childSource)) ∧
              HostedStrict result childResult ∧
              (result.Canonical → childResult.Canonical) ∧
              (∀ {signature} (wire : Var common signature),
                (∀ {pinSignature} (pin : Var pinWires pinSignature),
                  wire.index.val ≠ (pinCommon pin).index.val) →
                (result.incidencePaths wire.index.val ≠ [] ↔
                  childResult.incidencePaths wire.index.val ≠ [])) ∧
              (∀ {signature} (wire : Var pinWires signature),
                RegionPath.RootedTwo
                  (childResult.incidencePaths
                    (pinCommon wire).index.val)) ∧
              ((Region.ofItems (cutSupportedRootItems pinWires
                (WireRenaming.comp frame.sourceKeep pinCommon) source)
                    ).Canonical →
                (Region.ofItems childSource).Canonical) ∧
              (∀ {signature} (wire : Var common signature),
                Region.incidencePaths (frame.sourceKeep wire).index.val
                    (Region.ofItems (cutSupportedRootItems pinWires
                      (WireRenaming.comp frame.sourceKeep pinCommon) source)) ≠
                    [] ↔
                  (Region.ofItems childSource).incidencePaths
                    (frame.targetKeep wire).index.val ≠ []) ∧
              SupportParallelIncidenceScope
                (Region.incidencePaths frame.selected.index.val
                  (Region.ofItems (cutSupportedRootItems pinWires
                    (WireRenaming.comp frame.sourceKeep pinCommon) source)))
                ((Region.ofItems childSource).incidencePaths data.index.val) ∧
              (∀ {signature} (wire : Var pinWires signature),
                RegionPath.RootedTwo
                  ((Region.ofItems childSource).incidencePaths
                    (frame.targetKeep (pinCommon wire)).index.val)) := by
    cases evidence with
    | nil =>
        let childPattern := Erasure.Exposure.supportPattern body bodyCanonical
        let doubleCommon := cutDoubleRenaming pinCommon
        let emptyEdit : Transform.ItemsEdit (Content.Cut.operation wires)
            frame data .nil := .nil
        let emptyEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
            (pattern := childPattern) (retain := frame.targetKeep)
            (selected := data)
        obtain ⟨edit, target, pinResult, pinEvidence,
            ⟨pinIso⟩, pinBridge, ⟨pinPresentation⟩,
            pinEditCanonical, pinRetained, pinSelected⟩ :=
          cutPrependPinsFactor childPattern data invariant doubleCommon
            emptyEdit emptyEvidence ⟨RegionIso.refl _⟩
            (fun canonical => by simpa [emptyEdit,
              Transform.ItemsEdit.run] using canonical)
            (fun wire => by
              change SupportParallelIncidenceScope [] []
              exact SupportParallelIncidenceScope.refl [])
            (by
              change SupportParallelIncidenceScope [] []
              exact SupportParallelIncidenceScope.refl [])
        have sourceEq :
            (EqualityNormalization.allPins (pinWires ++ pinWires)
              (WireRenaming.comp frame.sourceKeep doubleCommon)).append .nil =
            cutSupportedRootItems pinWires
              (WireRenaming.comp frame.sourceKeep pinCommon) .nil := by
          simp only [cutSupportedRootItems, cutSupportedItems,
            ItemSeq.nil_append, ItemSeq.append_nil]
          rw [cutDoubleRenaming_comp]
        rw [← sourceEq]
        exact ⟨edit, target, pinResult, pinEvidence,
          ⟨pinIso⟩, pinBridge,
          (by
            intro _
            apply pinPresentation.canonical_iff.mp
            apply (Region.Canonical.conjoin_iff _ _).mpr
            constructor
            · constructor
              · intro localIndex
                exact Fin.elim0 localIndex
              · apply (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
                rw [cutAllPinsDouble]
                exact EqualityNormalization.allPins_twice_childrenCanonical
                  pinWires pinCommon
            · simp [Region.blank, Region.Canonical,
                ItemSeq.ChildrenCanonical]),
          (by
            intro signature wire disjoint
            have pinsEmpty :
                (EqualityNormalization.allPins (pinWires ++ pinWires)
                    doubleCommon).incidencePaths wire.index.val 0 = [] := by
              apply ItemSeq.pinWires_incidence_eq_nil_of
              intro pinSignature pin _maps
              apply Var.appendCases (left := pinWires) (right := pinWires)
                (motive := fun pin =>
                  (doubleCommon pin).index.val ≠ wire.index.val)
              · intro leftSignature left
                simpa [doubleCommon, cutDoubleRenaming] using
                  (disjoint left).symm
              · intro rightSignature right
                simpa [doubleCommon, cutDoubleRenaming] using
                  (disjoint right).symm
            have presentedEmpty :
                ((Region.ofItems
                    (EqualityNormalization.allPins (pinWires ++ pinWires)
                      doubleCommon)).conjoin
                    (Region.blank common)).incidencePaths wire.index.val = [] := by
              rw [Region.incidencePaths_conjoin,
                Region.incidencePaths_ofItems, pinsEmpty]
              simp [Region.blank, Region.incidencePaths,
                ItemSeq.incidencePaths]
            have pinLength := pinPresentation.incidencePaths_length_eq wire
            rw [presentedEmpty, List.length_nil] at pinLength
            have pinEmpty : pinResult.incidencePaths wire.index.val = [] :=
              List.length_eq_zero_iff.mp pinLength.symm
            simp [Region.blank, Region.incidencePaths,
              ItemSeq.incidencePaths, pinEmpty]),
          (by
            intro signature wire
            apply (pinPresentation.rootedTwo_incidencePaths_iff
              (pinCommon wire)).mp
            rw [Region.incidencePaths_conjoin,
              Region.incidencePaths_ofItems]
            apply RegionPath.RootedTwo.of_sublist
              (List.sublist_append_left _ _)
            rw [cutAllPinsDouble]
            exact EqualityNormalization.allPins_twice_rooted
              pinWires pinCommon wire 0),
          (fun sourceCanonical =>
            pinIso.canonical_iff.mp (pinEditCanonical sourceCanonical)),
          (fun wire =>
            (SupportParallelIncidenceScope.iso (RegionIso.refl _)
              pinIso (frame.sourceKeep wire) (frame.targetKeep wire)
              (pinRetained wire)).nonempty),
          (SupportParallelIncidenceScope.iso (RegionIso.refl _)
            pinIso frame.selected data pinSelected),
          (by
            intro signature wire
            apply (pinIso.rootedTwo_incidencePaths_iff
              (frame.targetKeep (pinCommon wire))).mp
            apply (pinRetained (pinCommon wire)).rooted
            rw [Region.incidencePaths_ofItems,
              cutDoubleRenaming_comp, cutAllPinsDouble]
            simpa only [ItemSeq.append_nil] using
              (EqualityNormalization.allPins_twice_rooted pinWires
                (WireRenaming.comp frame.sourceKeep pinCommon) wire 0))⟩
    | @cons _ _ _ _ item tail itemResult tailResult
        itemEvidence tailEvidence =>
        obtain ⟨itemEdit, childItem, childItemResult, childItemEvidence,
            ⟨itemIso⟩, itemBridge, itemCanonical, itemNonempty,
            itemSourceCanonical, itemSourceNonempty, itemSelectedScope⟩ :=
          cutItemFactor body bodyCanonical data invariant retainedSelected
            itemEvidence
        obtain ⟨tailEdit, childTail, childTailResult, childTailEvidence,
            ⟨tailIso⟩, tailBridge, tailCanonical, tailNonempty,
            tailRooted, tailSourceCanonical, tailSourceNonempty,
            tailSelectedScope, tailSourceRooted⟩ :=
          cutItemsFactor body bodyCanonical data invariant retainedSelected
            pinCommon tailEvidence
        let edit := Transform.ItemsEdit.cons itemEdit tailEdit
        let childSource := ItemSeq.cons childItem childTail
        let childResult := childItemResult.conjoin childTailResult
        let combinedIso := RegionIso.conjoinCongr itemIso tailIso
        let targetIso := combinedIso.trans
          (RegionIso.ofEq
            (Region.singleton_conjoin_ofItems childItem childTail))
        have supportedConsEq :
            cutSupportedRootItems pinWires
                (WireRenaming.comp frame.sourceKeep pinCommon) (.cons item tail) =
              .cons (cutSupportedItem item)
                (cutSupportedRootItems pinWires
                  (WireRenaming.comp frame.sourceKeep pinCommon) tail) := by
          rfl
        exact ⟨edit, childSource, childResult,
          VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
            childItemEvidence childTailEvidence,
          ⟨targetIso⟩,
          HostedStrict.conjoin _ _ _ _ itemBridge tailBridge,
          (by
            intro sourceCanonical
            have components :=
              (Region.Canonical.conjoin_iff _ _).mp sourceCanonical
            exact (Region.Canonical.conjoin_iff _ _).mpr
              ⟨itemCanonical components.1, tailCanonical components.2⟩),
          (by
            intro signature wire disjoint
            apply not_congr
            rw [Region.incidencePaths_conjoin,
              Region.incidencePaths_conjoin]
            have itemEmpty :
                childItemResult.incidencePaths wire.index.val = [] ↔
                  itemResult.incidencePaths wire.index.val = [] := by
              constructor
              · intro targetEmpty
                exact Classical.byContradiction (fun sourceNonempty =>
                  (itemNonempty wire).mp sourceNonempty targetEmpty)
              · intro sourceEmpty
                exact Classical.byContradiction (fun targetNonempty =>
                  (itemNonempty wire).mpr targetNonempty sourceEmpty)
            have tailEmpty :
                childTailResult.incidencePaths wire.index.val = [] ↔
                  tailResult.incidencePaths wire.index.val = [] := by
              constructor
              · intro targetEmpty
                exact Classical.byContradiction (fun sourceNonempty =>
                  (tailNonempty wire disjoint).mp sourceNonempty
                    targetEmpty)
              · intro sourceEmpty
                exact Classical.byContradiction (fun targetNonempty =>
                  (tailNonempty wire disjoint).mpr targetNonempty
                    sourceEmpty)
            constructor
            · intro sourceEmpty
              have sourceParts := List.append_eq_nil_iff.mp sourceEmpty
              have sourceTailEmpty :=
                (List.map_eq_nil_iff).mp sourceParts.2
              apply List.append_eq_nil_iff.mpr
              exact ⟨itemEmpty.mpr sourceParts.1,
                (List.map_eq_nil_iff).mpr
                  (tailEmpty.mpr sourceTailEmpty)⟩
            · intro targetEmpty
              have targetParts := List.append_eq_nil_iff.mp targetEmpty
              have targetTailEmpty :=
                (List.map_eq_nil_iff).mp targetParts.2
              apply List.append_eq_nil_iff.mpr
              exact ⟨itemEmpty.mp targetParts.1,
                (List.map_eq_nil_iff).mpr
                  (tailEmpty.mp targetTailEmpty)⟩),
          (by
            intro signature wire
            rw [Region.incidencePaths_conjoin]
            apply RegionPath.RootedTwo.of_sublist
              (List.sublist_append_right _ _)
            exact (RegionPath.RootedTwo.map_shiftHead_iff _ _).mpr
              (tailRooted wire)),
          (by
            intro sourceCanonical
            rw [supportedConsEq] at sourceCanonical
            rw [← Region.singleton_conjoin_ofItems] at sourceCanonical
            have components := (Region.Canonical.conjoin_iff _ _).mp
              sourceCanonical
            rw [← Region.singleton_conjoin_ofItems]
            exact (Region.Canonical.conjoin_iff _ _).mpr
              ⟨itemSourceCanonical components.1,
                tailSourceCanonical components.2⟩),
          (by
            intro signature wire
            rw [supportedConsEq,
              ← Region.singleton_conjoin_ofItems,
              ← Region.singleton_conjoin_ofItems,
              Region.incidencePaths_conjoin,
              Region.incidencePaths_conjoin]
            apply not_congr
            have itemEmpty :
                (Region.singleton childItem).incidencePaths
                    (frame.targetKeep wire).index.val = [] ↔
                  (Region.singleton (cutSupportedItem item)).incidencePaths
                    (frame.sourceKeep wire).index.val = [] := by
              constructor
              · intro targetEmpty
                exact Classical.byContradiction (fun sourceNonempty =>
                  (itemSourceNonempty wire).mp sourceNonempty targetEmpty)
              · intro sourceEmpty
                exact Classical.byContradiction (fun targetNonempty =>
                  (itemSourceNonempty wire).mpr targetNonempty sourceEmpty)
            have tailEmpty :
                (Region.ofItems childTail).incidencePaths
                    (frame.targetKeep wire).index.val = [] ↔
                  Region.incidencePaths (frame.sourceKeep wire).index.val
                    (Region.ofItems
                      (cutSupportedRootItems pinWires
                        (WireRenaming.comp frame.sourceKeep pinCommon) tail)) = [] := by
              constructor
              · intro targetEmpty
                exact Classical.byContradiction (fun sourceNonempty =>
                  (tailSourceNonempty wire).mp sourceNonempty targetEmpty)
              · intro sourceEmpty
                exact Classical.byContradiction (fun targetNonempty =>
                  (tailSourceNonempty wire).mpr targetNonempty sourceEmpty)
            constructor
            · intro sourceEmpty
              have parts := List.append_eq_nil_iff.mp sourceEmpty
              exact List.append_eq_nil_iff.mpr
                ⟨itemEmpty.mpr parts.1,
                  (List.map_eq_nil_iff).mpr
                    (tailEmpty.mpr ((List.map_eq_nil_iff).mp parts.2))⟩
            · intro targetEmpty
              have parts := List.append_eq_nil_iff.mp targetEmpty
              exact List.append_eq_nil_iff.mpr
                ⟨itemEmpty.mp parts.1,
                  (List.map_eq_nil_iff).mpr
                    (tailEmpty.mp ((List.map_eq_nil_iff).mp parts.2))⟩),
          (by
            rw [supportedConsEq,
              ← Region.singleton_conjoin_ofItems,
              ← Region.singleton_conjoin_ofItems]
            exact SupportParallelIncidenceScope.conjoin frame.selected data
              itemSelectedScope tailSelectedScope),
          (by
            intro signature wire
            rw [← Region.singleton_conjoin_ofItems,
              Region.incidencePaths_conjoin]
            apply RegionPath.RootedTwo.of_sublist
              (List.sublist_append_right _ _)
            exact (RegionPath.RootedTwo.map_shiftHead_iff _ _).mpr
              (tailSourceRooted wire))⟩
  termination_by sizeOf source

  theorem cutItemFactor
      {wires common actualWires : List Sig}
      (body : Region wires) (bodyCanonical : body.Canonical)
      {frame : Transform.Frame wires common actualWires actualWires}
      (data : (Content.Cut.operation wires).Data frame)
      (invariant : Transform.IndexedHeadInvariant frame data)
      (retainedSelected : ∀ {signature} (wire : Var common signature),
        (frame.sourceKeep wire).index.val ≠ frame.selected.index.val)
      {source : Item actualWires} {result : Region common}
      (evidence :
        VisualProof.Rule.Comprehension.Instantiation.ItemResult
          (Erasure.Exposure.supportPattern (Region.singleton (.cut body))
            ((Region.singleton_cut_canonical_iff body).mpr bodyCanonical))
          frame.sourceKeep frame.selected source result) :
      ∃ edit : Transform.ItemEdit (Content.Cut.operation wires)
          frame data (cutSupportedItem source),
        ∃ childSource : Item actualWires,
          ∃ childResult : Region common,
            VisualProof.Rule.Comprehension.Instantiation.ItemResult
                (Erasure.Exposure.supportPattern body bodyCanonical)
                frame.targetKeep data childSource childResult ∧
              Nonempty (RegionIso (WireEquiv.refl actualWires)
                edit.run (Region.singleton childSource)) ∧
              HostedStrict result childResult ∧
              (result.Canonical → childResult.Canonical) ∧
              (∀ {signature} (wire : Var common signature),
                result.incidencePaths wire.index.val ≠ [] ↔
                  childResult.incidencePaths wire.index.val ≠ []) ∧
              ((Region.singleton (cutSupportedItem source)).Canonical →
                (Region.singleton childSource).Canonical) ∧
              (∀ {signature} (wire : Var common signature),
                (Region.singleton (cutSupportedItem source)).incidencePaths
                      (frame.sourceKeep wire).index.val ≠ [] ↔
                  (Region.singleton childSource).incidencePaths
                      (frame.targetKeep wire).index.val ≠ []) ∧
              SupportParallelIncidenceScope
                ((Region.singleton (cutSupportedItem source)).incidencePaths
                  frame.selected.index.val)
                ((Region.singleton childSource).incidencePaths
                  data.index.val) := by
    cases evidence with
    | atom head ports =>
        have headEq : frame.sourceKeep head = frame.targetKeep head := by
          apply Var.eq_of_index_eq
          apply Fin.ext
          exact invariant.2.1 head
        have portsEq :
            ports.map (fun wire => frame.sourceKeep wire) =
              ports.map (fun wire => frame.targetKeep wire) := by
          apply Vars.map_congr
          intro signature wire
          apply Var.eq_of_index_eq
          apply Fin.ext
          exact invariant.2.1 wire
        have itemEq :
            cutSupportedItem (.atom (frame.sourceKeep head)
              (ports.map fun wire => frame.sourceKeep wire)) =
              .atom (frame.targetKeep head)
                (ports.map fun wire => frame.targetKeep wire) := by
          simp only [cutSupportedItem]
          rw [headEq, portsEq]
        exact ⟨.atom head ports,
          .atom (frame.targetKeep head)
            (ports.map fun wire => frame.targetKeep wire),
          Region.singleton (.atom head ports),
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.atom
            head ports,
          ⟨RegionIso.refl _⟩, HostedStrict.refl _,
          (fun canonical => canonical), (fun _ => Iff.rfl),
          (by
            rw [itemEq]
            exact fun canonical => canonical),
          (by
            intro signature wire
            simp [itemEq, invariant.2.1 wire]),
          (by
            simpa [itemEq, invariant.2.2] using
              (SupportParallelIncidenceScope.refl
                ((Region.singleton
                  (.atom (frame.targetKeep head)
                    (ports.map fun wire => frame.targetKeep wire))).incidencePaths
                      data.index.val)))⟩
    | selectedAtom ports =>
        let childPattern := Erasure.Exposure.supportPattern body bodyCanonical
        let emptyRename : WireRenaming common (common ++ []) :=
          (WireEquiv.appendNil common).symm.toRenaming
        let liftedPorts := ports.map fun wire => emptyRename wire
        let selectedEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.selectedAtom
            (pattern := childPattern)
            (retain := frame.targetKeep.appendRight [])
            (selected := data.appendLeft []) liftedPorts
        let childEvidence :=
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            (VisualProof.Rule.Comprehension.Instantiation.RegionResult.mk
              (VisualProof.Rule.Comprehension.Instantiation.ItemsResult.cons
                selectedEvidence
                (VisualProof.Rule.Comprehension.Instantiation.ItemsResult.nil
                  (pattern := childPattern)
                  (retain := frame.targetKeep.appendRight [])
                  (selected := data.appendLeft []))))
        let childBody : Region actualWires :=
          .mk [] (.cons
            (.atom (data.appendLeft [])
              (liftedPorts.map fun wire =>
                (frame.targetKeep.appendRight []) wire)) .nil)
        let childSource : Item actualWires := .cut childBody
        let instantiated :=
          VisualProof.Rule.Comprehension.Instantiation.instantiate
            childPattern liftedPorts
        let childResult : Region common := Region.singleton (.cut
          (Region.adjoinAt [] .nil
            (instantiated.conjoin (Region.blank (common ++ [])))))
        have evidenceExact :
            VisualProof.Rule.Comprehension.Instantiation.ItemResult
              childPattern frame.targetKeep data childSource childResult := by
          exact childEvidence
        let edit : Transform.ItemEdit (Content.Cut.operation wires)
            frame data (.atom frame.selected
              (ports.map fun wire => frame.sourceKeep wire)) :=
          .selectedAtom ports PUnit.unit
        have portsEq :
            (ports.map fun wire => (frame.targetKeep wire).appendLeft []) =
              liftedPorts.map fun wire =>
                (frame.targetKeep.appendRight []) wire := by
          simp only [liftedPorts, Vars.map_map]
          apply Vars.map_congr
          intro signature wire
          simp [emptyRename, WireRenaming.appendRight,
            WireEquiv.appendNil_symm_apply]
        have sourceEq : edit.run = Region.singleton childSource := by
          simp only [edit, Transform.ItemEdit.run, Content.Cut.operation,
            childSource, childBody, liftedPorts, emptyRename,
            Region.singleton, Region.ofItems, ItemSeq.renameWires,
            Item.renameWires, Vars.map_map]
          congr 6
          congr 1
          simpa only [liftedPorts, Vars.map_map] using portsEq
        let direct :=
          VisualProof.Rule.Comprehension.Instantiation.instantiate
            childPattern ports
        have renamedEq : direct.renameWires emptyRename = instantiated := by
          simpa only [direct, instantiated, liftedPorts] using
            EqualityNormalization.instantiate_renameWires
              childPattern ports emptyRename
        let materialIso : RegionIso (WireEquiv.refl (common ++ []))
            (direct.renameWires emptyRename)
            (instantiated.conjoin (Region.blank (common ++ []))) :=
          (RegionIso.ofEq renamedEq).trans
            (RegionIso.conjoinBlank instantiated).symm
        let bodyIso : RegionIso (WireEquiv.refl common)
            direct (Region.adjoinAt [] .nil
              (instantiated.conjoin (Region.blank (common ++ [])))) :=
          (RegionIso.adjoinAtNilRenamed direct).trans
            (RegionIso.adjoinAt [] .nil materialIso)
        let targetIso := RegionIso.singletonCutCongr bodyIso
        let resultBridge := HostedStrict.iso (RegionIso.refl _) targetIso
          (supportCutInstantiatedHosted body bodyCanonical ports)
        have targetRetainedSelected : ∀ {signature}
            (wire : Var common signature),
            (frame.targetKeep wire).index.val ≠ data.index.val := by
          intro signature wire equal
          apply retainedSelected wire
          rw [invariant.2.1 wire, invariant.2.2]
          exact equal
        exact ⟨edit, childSource, childResult, evidenceExact,
          ⟨RegionIso.ofEq sourceEq⟩, resultBridge,
          (by
            intro _sourceCanonical
            apply targetIso.canonical_iff.mp
            exact (Region.singleton_cut_canonical_iff direct).mpr
              (VisualProof.Rule.Comprehension.Instantiation.instantiate_canonical
                childPattern ports)),
          (by
            intro signature wire
            have targetLength := targetIso.incidencePaths_length_eq wire
            rw [Region.incidencePaths_singleton_cut] at targetLength
            simp only [List.length_map] at targetLength
            change (direct.incidencePaths wire.index.val).length =
              (childResult.incidencePaths wire.index.val).length
                at targetLength
            constructor
            · intro sourceNonempty
              have countPositive : 0 < ports.countIndex wire.index.val := by
                rw [← EqualityNormalization.instantiate_incidence_nonempty_iff
                  (Erasure.Exposure.supportPattern
                    (Region.singleton (.cut body))
                    ((Region.singleton_cut_canonical_iff body).mpr
                      bodyCanonical)) ports wire]
                exact sourceNonempty
              have directNonempty : direct.incidencePaths
                  wire.index.val ≠ [] := by
                rw [EqualityNormalization.instantiate_incidence_nonempty_iff]
                exact countPositive
              rw [← List.length_pos_iff] at directNonempty ⊢
              omega
            · intro targetNonempty
              rw [← List.length_pos_iff] at targetNonempty
              have directNonempty : direct.incidencePaths
                  wire.index.val ≠ [] := by
                rw [← List.length_pos_iff]
                omega
              have countPositive : 0 < ports.countIndex wire.index.val := by
                rw [← EqualityNormalization.instantiate_incidence_nonempty_iff
                  childPattern ports wire]
                exact directNonempty
              rw [EqualityNormalization.instantiate_incidence_nonempty_iff]
              exact countPositive),
          (by
            intro _
            apply (Region.singleton_cut_canonical_iff childBody).mpr
            simp [childBody, Region.Canonical,
              ItemSeq.ChildrenCanonical, Item.ChildrenCanonical]),
          (by
            intro signature wire
            rw [← sourceEq]
            let sourceAtom : Item actualWires :=
              .atom frame.selected
                (ports.map fun port => frame.sourceKeep port)
            let targetAtom : Item actualWires :=
              .atom data (ports.map fun port => frame.targetKeep port)
            have mappedPortsEq :
                (ports.map fun port => frame.sourceKeep port).countIndex
                    (frame.sourceKeep wire).index.val =
                  (ports.map fun port => frame.targetKeep port).countIndex
                    (frame.targetKeep wire).index.val := by
              have countEq := Vars.countIndex_map_eq_of_index_eq ports
                (fun port => frame.sourceKeep port)
                (fun port => frame.targetKeep port)
                (fun port => invariant.2.1 port)
                (frame.sourceKeep wire).index.val
              simpa only [invariant.2.1 wire] using countEq
            have sourceAtomPaths :
                (Region.singleton sourceAtom).incidencePaths
                    (frame.sourceKeep wire).index.val =
                  List.replicate
                    ((if frame.selected.index.val =
                        (frame.sourceKeep wire).index.val then 1 else 0) +
                      (ports.map fun port => frame.sourceKeep port).countIndex
                        (frame.sourceKeep wire).index.val) [] := by
              let appendNil : WireRenaming actualWires (actualWires ++ []) :=
                ⟨fun inherited => inherited.appendLeft []⟩
              have renamed :=
                ItemSeq.incidencePaths_renameWires_preservesIndex
                  (.cons sourceAtom .nil) appendNil (by simp)
                  (by intro inheritedSignature inherited; simp [appendNil])
                  (frame.sourceKeep wire) 0
              simpa [sourceAtom, Region.singleton, Region.ofItems,
                Region.incidencePaths, ItemSeq.incidencePaths,
                Item.incidencePaths, appendNil] using renamed
            have targetAtomPaths :
                (Region.singleton targetAtom).incidencePaths
                    (frame.targetKeep wire).index.val =
                  List.replicate
                    ((if data.index.val =
                        (frame.targetKeep wire).index.val then 1 else 0) +
                      (ports.map fun port => frame.targetKeep port).countIndex
                        (frame.targetKeep wire).index.val) [] := by
              let appendNil : WireRenaming actualWires (actualWires ++ []) :=
                ⟨fun inherited => inherited.appendLeft []⟩
              have renamed :=
                ItemSeq.incidencePaths_renameWires_preservesIndex
                  (.cons targetAtom .nil) appendNil (by simp)
                  (by intro inheritedSignature inherited; simp [appendNil])
                  (frame.targetKeep wire) 0
              simpa [targetAtom, Region.singleton, Region.ofItems,
                Region.incidencePaths, ItemSeq.incidencePaths,
                Item.incidencePaths, appendNil] using renamed
            change (Region.singleton sourceAtom).incidencePaths
                (frame.sourceKeep wire).index.val ≠ [] ↔
              (Region.singleton (.cut (Region.singleton targetAtom))).incidencePaths
                (frame.targetKeep wire).index.val ≠ []
            rw [sourceAtomPaths, Region.incidencePaths_singleton_cut,
              targetAtomPaths]
            have sourceHeadNe : frame.selected.index.val ≠
                (frame.sourceKeep wire).index.val :=
              (retainedSelected wire).symm
            have targetHeadNe : data.index.val ≠
                (frame.targetKeep wire).index.val :=
              (targetRetainedSelected wire).symm
            simp [sourceHeadNe, targetHeadNe, mappedPortsEq]),
          (by
            have sourcePaths :
                (Region.singleton (cutSupportedItem
                  (.atom frame.selected
                    (ports.map fun wire => frame.sourceKeep wire)))).incidencePaths
                    frame.selected.index.val = [[]] := by
              have portsZero :
                  (ports.map fun wire => frame.sourceKeep wire).countIndex
                      frame.selected.index.val = 0 :=
                Vars.countIndex_map_eq_zero_of_no_preimage ports
                  frame.sourceKeep frame.selected.index.val
                  (fun wire => retainedSelected wire)
              let appendNil : WireRenaming actualWires (actualWires ++ []) :=
                ⟨fun wire => wire.appendLeft []⟩
              have renamed :=
                ItemSeq.incidencePaths_renameWires_preservesIndex
                  (.cons (.atom frame.selected
                    (ports.map fun wire => frame.sourceKeep wire)) .nil)
                  appendNil (by simp)
                  (by intro inheritedSignature inherited; simp [appendNil])
                  frame.selected 0
              simpa [cutSupportedItem, Region.singleton, Region.ofItems,
                Region.incidencePaths, ItemSeq.incidencePaths,
                Item.incidencePaths, appendNil, portsZero] using renamed
            have targetPaths :
                (Region.singleton childSource).incidencePaths
                    data.index.val = [[0]] := by
              let targetAtom := Region.singleton
                (.atom data (ports.map fun wire => frame.targetKeep wire))
              have atomPaths : targetAtom.incidencePaths data.index.val = [[]] := by
                have portsZero :
                    (ports.map fun wire => frame.targetKeep wire).countIndex
                        data.index.val = 0 :=
                  Vars.countIndex_map_eq_zero_of_no_preimage ports
                    frame.targetKeep data.index.val
                    (fun wire => targetRetainedSelected wire)
                let appendNil : WireRenaming actualWires (actualWires ++ []) :=
                  ⟨fun wire => wire.appendLeft []⟩
                have renamed :=
                  ItemSeq.incidencePaths_renameWires_preservesIndex
                    (.cons (.atom data
                      (ports.map fun wire => frame.targetKeep wire)) .nil)
                    appendNil (by simp)
                    (by intro inheritedSignature inherited; simp [appendNil])
                    data 0
                simpa [targetAtom, Region.singleton, Region.ofItems,
                  Region.incidencePaths, ItemSeq.incidencePaths,
                  Item.incidencePaths, appendNil, portsZero] using
                    renamed
              rw [← sourceEq]
              change (Region.singleton (.cut targetAtom)).incidencePaths
                data.index.val = [[0]]
              rw [Region.incidencePaths_singleton_cut, atomPaths]
              rfl
            rw [sourcePaths, targetPaths]
            constructor
            · simp
            · intro rooted
              simp [RegionPath.RootedTwo] at rooted)⟩
    | identity signature arity ports =>
        have portsEq :
            (fun index => frame.sourceKeep (ports index)) =
              (fun index => frame.targetKeep (ports index)) := by
          funext index
          apply Var.eq_of_index_eq
          apply Fin.ext
          exact invariant.2.1 (ports index)
        have itemEq :
            cutSupportedItem (.identity signature arity
              (fun index => frame.sourceKeep (ports index))) =
              .identity signature arity
                (fun index => frame.targetKeep (ports index)) := by
          simp only [cutSupportedItem]
          rw [portsEq]
        exact ⟨.identity signature arity ports,
          .identity signature arity
            (fun index => frame.targetKeep (ports index)),
          Region.singleton (.identity signature arity ports),
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.identity
            signature arity ports,
          ⟨RegionIso.refl _⟩, HostedStrict.refl _,
          (fun canonical => canonical), (fun _ => Iff.rfl),
          (by simp [itemEq]),
          (by
            intro signature wire
            simp [itemEq, invariant.2.1 wire]),
          (by
            simpa [itemEq, invariant.2.2] using
              (SupportParallelIncidenceScope.refl
                ((Region.singleton
                  (.identity signature arity
                    (fun index => frame.targetKeep (ports index)))).incidencePaths
                      data.index.val)))⟩
    | cut childEvidence =>
        obtain ⟨childEdit, childSource, childResult, childResultEvidence,
            ⟨childIso⟩, childBridge, childCanonical, childNonempty,
            sourceCanonical, sourceNonempty, selectedScope⟩ :=
          cutRegionFactor body bodyCanonical data invariant retainedSelected
            childEvidence
        exact ⟨.cut childEdit, .cut childSource,
          Region.singleton (.cut childResult),
          VisualProof.Rule.Comprehension.Instantiation.ItemResult.cut
            childResultEvidence,
          ⟨RegionIso.singletonCutCongr childIso⟩,
          HostedStrict.cut _ _ childBridge,
          (by
            intro sourceCanonical
            exact (Region.singleton_cut_canonical_iff childResult).mpr
              (childCanonical
                ((Region.singleton_cut_canonical_iff _).mp sourceCanonical))),
          (by
            intro signature wire
            rw [Region.incidencePaths_singleton_cut,
              Region.incidencePaths_singleton_cut]
            constructor
            · intro sourceNonempty targetEmpty
              exact (childNonempty wire).mp
                (fun sourceEmpty => sourceNonempty
                  ((List.map_eq_nil_iff).mpr sourceEmpty))
                ((List.map_eq_nil_iff).mp targetEmpty)
            · intro targetNonempty sourceEmpty
              exact (childNonempty wire).mpr
                (fun targetEmpty => targetNonempty
                ((List.map_eq_nil_iff).mpr targetEmpty))
                ((List.map_eq_nil_iff).mp sourceEmpty)),
          (by
            intro canonical
            exact (Region.singleton_cut_canonical_iff childSource).mpr
              (sourceCanonical
                ((Region.singleton_cut_canonical_iff _).mp canonical))),
          (by
            intro signature wire
            simp only [cutSupportedItem,
              Region.incidencePaths_singleton_cut]
            simpa only [ne_eq, List.map_eq_nil_iff] using
              (sourceNonempty wire)),
          SupportParallelIncidenceScope.cut frame.selected data
            selectedScope⟩
  termination_by sizeOf source
end

/-- The cut constructor is derivable from the recursively derived body. -/
theorem supportCutDerives
    {wires : List Sig} (body : Region wires)
    (bodyIH : SupportDerives body) :
    SupportDerives (Region.singleton (.cut body)) := by
  intro materialCanonical structuralOuter structuralBefore structuralAfter
    items result evidence request
  have bodyCanonical :=
    (Region.singleton_cut_canonical_iff body).mp materialCanonical
  let oldLocals := structuralBefore ++ structuralAfter
  let pendingLocals := structuralBefore ++ .rel wires :: structuralAfter
  let common := structuralOuter ++ oldLocals
  let frame := Content.Cut.rootFrame structuralOuter structuralBefore
    structuralAfter wires
  let data := Content.Cut.targetHead structuralOuter structuralBefore
    structuralAfter wires
  let pinCommon : WireRenaming oldLocals common :=
    ⟨fun wire => Var.appendRight structuralOuter wire⟩
  have invariant : Transform.IndexedHeadInvariant frame data := by
    constructor
    · rfl
    · constructor
      · intro signature wire
        rfl
      · rfl
  have retainedSelected : ∀ {signature} (wire : Var common signature),
      (frame.sourceKeep wire).index.val ≠ frame.selected.index.val := by
    intro signature wire
    exact Transform.Frame.insertedHead_ne_keep
      (outer := structuralOuter) (before := structuralBefore)
      (after := structuralAfter) (selectedSignature := .rel wires)
      (inserted := []) wire |>.symm
  obtain ⟨edit, childItems, childResult, childEvidence, ⟨childIso⟩,
      resultBridge, resultCanonical, resultNonempty, resultRooted,
      childSourceCanonical, childSourceNonempty, childSelectedScope,
      childSourceRooted⟩ :=
    cutItemsFactor body bodyCanonical data invariant retainedSelected
      pinCommon evidence
  let supportedItems := cutSupportedRootItems oldLocals
    (WireRenaming.comp frame.sourceKeep pinCommon) items
  let originalPending : Region structuralOuter := .mk pendingLocals items
  let supportedPending : Region structuralOuter :=
    .mk pendingLocals supportedItems
  let childPending : Region structuralOuter := .mk pendingLocals childItems
  let fullInstantiated : Region structuralOuter :=
    Region.adjoinAt oldLocals .nil result
  let recursiveInstantiated : Region structuralOuter :=
    Region.adjoinAt oldLocals .nil childResult
  have fullLocalCanonical : fullInstantiated.Canonical :=
    request.occurrence.context.holeCanonical fullInstantiated
      (by simpa only [fullInstantiated, oldLocals] using
        request.instantiatedCanonical)
  have resultMaterialCanonical : result.Canonical :=
    Region.Canonical.material_of_adjoinAt oldLocals .nil result
      (by simpa only [fullInstantiated] using fullLocalCanonical)
  have recursiveLocalCanonical : recursiveInstantiated.Canonical := by
    apply Region.Canonical.adjoinAt_of_material_roots oldLocals .nil
      childResult True.intro (resultCanonical resultMaterialCanonical)
    intro localIndex
    let localWire : Var oldLocals (oldLocals.get localIndex) :=
      Var.ofIndex localIndex
    have rooted := resultRooted localWire
    simpa [recursiveInstantiated, pinCommon, common, localWire] using rooted
  have instantiatedNonempty : ∀ {signature}
      (wire : Var structuralOuter signature),
      fullInstantiated.incidencePaths wire.index.val ≠ [] ↔
        recursiveInstantiated.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    let commonWire := wire.appendLeft oldLocals
    have inherited := resultNonempty commonWire (by
      intro pinSignature pin
      simp [commonWire, pinCommon]
      omega)
    have sourcePaths := Region.incidencePaths_adjoinAt_nil result commonWire
    have targetPaths := Region.incidencePaths_adjoinAt_nil childResult commonWire
    change
      (Region.adjoinAt oldLocals .nil result).incidencePaths
          wire.index.val ≠ [] ↔
        (Region.adjoinAt oldLocals .nil childResult).incidencePaths
          wire.index.val ≠ []
    rw [show wire.index.val = commonWire.index.val by simp [commonWire],
      sourcePaths, targetPaths]
    simpa [frame, commonWire, Content.Cut.rootFrame,
      Transform.Frame.replace] using inherited
  have recursiveValidity := filledValidityOfReplacement
    request.occurrence.interface request.occurrence.context
    fullInstantiated recursiveInstantiated
    (by simpa only [fullInstantiated, oldLocals] using
      request.instantiatedCanonical)
    (by
      intro signature wire
      simpa only [fullInstantiated, oldLocals] using
        request.instantiatedExternalTwoEnded wire)
    recursiveLocalCanonical instantiatedNonempty
  have polarityEq : request.occurrence.context.polarity = request.polarity :=
    request.continuation.1
  have instantiatedBridge : HostedStrict fullInstantiated
      recursiveInstantiated := by
    simpa only [fullInstantiated, recursiveInstantiated] using
      HostedStrict.adjoinAt oldLocals result childResult resultBridge
  have resultBridgeTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      fullInstantiated recursiveInstantiated
      (by simpa only [fullInstantiated, oldLocals] using
        request.instantiatedCanonical)
      (by
        intro signature wire
        simpa only [fullInstantiated, oldLocals] using
          request.instantiatedExternalTwoEnded wire)
      recursiveValidity.1 recursiveValidity.2 :=
    telescopeOfHostedExact instantiatedBridge request.polarity
      request.occurrence.interface request.occurrence.context
      (by simpa only [fullInstantiated, oldLocals] using
        request.instantiatedCanonical)
      (by
        intro signature wire
        simpa only [fullInstantiated, oldLocals] using
          request.instantiatedExternalTwoEnded wire)
      recursiveValidity.1 recursiveValidity.2 polarityEq
  have originalLocalCanonical : originalPending.Canonical :=
    request.occurrence.context.holeCanonical originalPending
      (by simpa only [originalPending, pendingLocals] using
        request.pendingCanonical)
  have originalMaterialCanonical : (Region.ofItems items).Canonical := by
    have adjoinedCanonical :
        (Region.adjoinAt pendingLocals .nil
          (Region.ofItems items)).Canonical :=
      (RegionIso.adjoinAtOfItems pendingLocals items).canonical_iff.mpr
        originalLocalCanonical
    exact Region.Canonical.material_of_adjoinAt pendingLocals .nil
      (Region.ofItems items) adjoinedCanonical
  have deepMaterialCanonical :
      (Region.ofItems (cutSupportedItems items)).Canonical :=
    (cutSupportedItemsScope items).canonical originalMaterialCanonical
  let rootRename := WireRenaming.comp frame.sourceKeep pinCommon
  let rootPins := EqualityNormalization.allPins (oldLocals ++ oldLocals)
    (cutDoubleRenaming rootRename)
  have rootPinsCanonical : (Region.ofItems rootPins).Canonical := by
    constructor
    · intro localIndex
      exact Fin.elim0 localIndex
    · apply (ItemSeq.ChildrenCanonical.renameWires_iff _ _).mpr
      change rootPins.ChildrenCanonical
      rw [show rootPins =
          (EqualityNormalization.allPins oldLocals rootRename).append
            (EqualityNormalization.allPins oldLocals rootRename) by
        simp only [rootPins]
        exact cutAllPinsDouble oldLocals rootRename]
      exact EqualityNormalization.allPins_twice_childrenCanonical
        oldLocals rootRename
  have supportedMaterialCanonical :
      (Region.ofItems supportedItems).Canonical := by
    change (Region.ofItems
      ((cutSupportedItems items).append rootPins)).Canonical
    rw [← Region.ofItems_conjoin]
    exact (Region.Canonical.conjoin_iff _ _).mpr
      ⟨deepMaterialCanonical, rootPinsCanonical⟩
  have supportedLocalCanonical : supportedPending.Canonical := by
    let presentation := RegionIso.adjoinAtOfItems pendingLocals supportedItems
    apply presentation.canonical_iff.mp
    apply Region.Canonical.adjoinAt_of_material_roots pendingLocals .nil
      (Region.ofItems supportedItems) True.intro supportedMaterialCanonical
    intro localIndex
    let localWire : Var pendingLocals (pendingLocals.get localIndex) :=
      Var.ofIndex localIndex
    let actualWire := Var.appendRight structuralOuter localWire
    have originalRoot := originalLocalCanonical.1 localIndex
    have materialRoot : RegionPath.RootedTwo
        ((Region.ofItems items).incidencePaths actualWire.index.val) := by
      rw [Region.incidencePaths_ofItems]
      simpa [actualWire, localWire, pendingLocals] using originalRoot
    have deepRoot :=
      (cutSupportedItemsScope items).rootedTwo actualWire materialRoot
    have joinedRoot : RegionPath.RootedTwo
        (((Region.ofItems (cutSupportedItems items)).conjoin
          (Region.ofItems rootPins)).incidencePaths actualWire.index.val) := by
      rw [Region.incidencePaths_conjoin]
      exact RegionPath.RootedTwo.of_sublist
        (List.sublist_append_left _ _) deepRoot
    have supportedRoot : RegionPath.RootedTwo
        ((Region.ofItems supportedItems).incidencePaths
          actualWire.index.val) := by
      change RegionPath.RootedTwo
        ((Region.ofItems
          ((cutSupportedItems items).append rootPins)).incidencePaths
            actualWire.index.val)
      rw [← Region.ofItems_conjoin]
      exact joinedRoot
    simpa [actualWire, localWire] using supportedRoot
  have originalSupportedNonempty : ∀ {signature}
      (wire : Var structuralOuter signature),
      originalPending.incidencePaths wire.index.val ≠ [] ↔
        supportedPending.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    let actualWire := wire.appendLeft pendingLocals
    have rootPinsEmpty :
        rootPins.incidencePaths actualWire.index.val 0 = [] := by
      have pinNotOuter : ∀ {pinSignature}
          (pin : Var oldLocals pinSignature),
          (rootRename pin).index.val ≠ actualWire.index.val := by
        intro pinSignature pin equal
        let outerCommon := wire.appendLeft oldLocals
        have outerImage :
            (frame.sourceKeep outerCommon).index.val =
              actualWire.index.val := by
          simp [frame, outerCommon, actualWire, oldLocals, pendingLocals,
            Content.Cut.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep]
        have keptEqual :
            (frame.sourceKeep (pinCommon pin)).index.val =
              (frame.sourceKeep outerCommon).index.val := by
          exact equal.trans outerImage.symm
        have commonEqual :=
          (Transform.Frame.keep_index_eq_iff
            (outer := structuralOuter) (before := structuralBefore)
            (inserted := [.rel wires]) (after := structuralAfter)
            (pinCommon pin) outerCommon).mp keptEqual
        simp [pinCommon, outerCommon, oldLocals] at commonEqual
        omega
      rw [show rootPins =
          (EqualityNormalization.allPins oldLocals rootRename).append
            (EqualityNormalization.allPins oldLocals rootRename) by
        simp only [rootPins]
        exact cutAllPinsDouble oldLocals rootRename]
      rw [ItemSeq.incidencePaths_append]
      have once :
          ItemSeq.incidencePaths actualWire.index.val 0
            (EqualityNormalization.allPins oldLocals rootRename) = [] := by
        apply ItemSeq.pinWires_incidence_eq_nil_of
        intro pinSignature pin _maps
        exact pinNotOuter pin
      have twice :
          ItemSeq.incidencePaths actualWire.index.val
            (EqualityNormalization.allPins oldLocals rootRename).length
            (EqualityNormalization.allPins oldLocals rootRename) = [] := by
        apply ItemSeq.pinWires_incidence_eq_nil_of
        intro pinSignature pin _maps
        exact pinNotOuter pin
      rw [once, Nat.zero_add, twice]
      rfl
    have deepNonempty :=
      (cutSupportedItemsScope items).incidenceNonempty actualWire
    change items.incidencePaths wire.index.val 0 ≠ [] ↔
      supportedItems.incidencePaths wire.index.val 0 ≠ []
    rw [show wire.index.val = actualWire.index.val by simp [actualWire],
      show supportedItems = (cutSupportedItems items).append rootPins by rfl,
      EqualityNormalization.ItemSeq.incidencePaths_append_nonempty_iff,
      rootPinsEmpty]
    simp only [ne_eq, not_true_eq_false, or_false]
    simpa only [Region.incidencePaths_ofItems] using deepNonempty
  have supportedValidity := filledValidityOfReplacement
    request.occurrence.interface request.occurrence.context
    originalPending supportedPending
    (by simpa only [originalPending, pendingLocals] using
      request.pendingCanonical)
    (by
      intro signature wire
      simpa only [originalPending, pendingLocals] using
        request.pendingExternalTwoEnded wire)
    supportedLocalCanonical originalSupportedNonempty
  have childMaterialCanonical : (Region.ofItems childItems).Canonical :=
    childSourceCanonical (by
      simpa only [supportedItems] using supportedMaterialCanonical)
  let selectedIndex : Fin pendingLocals.length :=
    ⟨structuralBefore.length, by simp [pendingLocals]⟩
  have sourceSelectedRoot : RegionPath.RootedTwo
      ((Region.ofItems supportedItems).incidencePaths
        frame.selected.index.val) := by
    rw [Region.incidencePaths_ofItems]
    simpa [selectedIndex, frame, pendingLocals, Content.Cut.rootFrame,
      Transform.Frame.replace, Transform.Frame.insertedHead] using
        (supportedLocalCanonical.1 selectedIndex)
  have targetSelectedRoot : RegionPath.RootedTwo
      ((Region.ofItems childItems).incidencePaths data.index.val) :=
    childSelectedScope.rooted sourceSelectedRoot
  have childLocalCanonical : childPending.Canonical := by
    let presentation := RegionIso.adjoinAtOfItems pendingLocals childItems
    apply presentation.canonical_iff.mp
    apply Region.Canonical.adjoinAt_of_material_roots pendingLocals .nil
      (Region.ofItems childItems) True.intro childMaterialCanonical
    intro localIndex
    by_cases beforeCase : localIndex.val < structuralBefore.length
    · let beforeIndex : Fin structuralBefore.length :=
        ⟨localIndex.val, beforeCase⟩
      let oldWire := (Var.ofIndex beforeIndex).appendLeft structuralAfter
      have rooted := childSourceRooted oldWire
      have indexEq :
          (frame.targetKeep (pinCommon oldWire)).index.val =
            structuralOuter.length + localIndex.val := by
        simp [frame, pinCommon, oldLocals, oldWire, beforeIndex,
          Content.Cut.rootFrame, Transform.Frame.replace,
          Transform.Frame.keep, Transform.Frame.localKeep]
      rw [← indexEq]
      exact rooted
    · by_cases selectedCase : localIndex.val = structuralBefore.length
      · simpa [data, selectedCase, Content.Cut.targetHead,
          Transform.Frame.insertedHead] using targetSelectedRoot
      · have afterBound :
          localIndex.val - structuralBefore.length - 1 <
            structuralAfter.length := by
          have bound := localIndex.isLt
          simp [pendingLocals] at bound
          omega
        let afterIndex : Fin structuralAfter.length :=
          ⟨localIndex.val - structuralBefore.length - 1, afterBound⟩
        let oldWire := Var.appendRight structuralBefore
          (Var.ofIndex afterIndex)
        have rooted := childSourceRooted oldWire
        have rawIndexEq :
            (frame.targetKeep (pinCommon oldWire)).index.val =
              structuralOuter.length +
                (structuralBefore.length +
                  (Var.appendRight [.rel wires]
                    (Var.ofIndex afterIndex)).index.val) := by
          simp [frame, pinCommon, oldLocals, oldWire,
            Content.Cut.rootFrame, Transform.Frame.replace,
            Transform.Frame.keep, Transform.Frame.localKeep]
        have liftedIndex :
            (Var.appendRight [.rel wires]
              (Var.ofIndex afterIndex)).index.val =
                1 + afterIndex.val := by
          simpa using (Var.index_appendRight [.rel wires]
            (Var.ofIndex afterIndex))
        have indexEq :
            (frame.targetKeep (pinCommon oldWire)).index.val =
              structuralOuter.length + localIndex.val := by
          calc
            _ = structuralOuter.length +
                (structuralBefore.length +
                  (Var.appendRight [.rel wires]
                    (Var.ofIndex afterIndex)).index.val) := rawIndexEq
            _ = structuralOuter.length +
                (structuralBefore.length + (1 + afterIndex.val)) :=
              congrArg (fun index => structuralOuter.length +
                (structuralBefore.length + index)) liftedIndex
            _ = structuralOuter.length + localIndex.val := by
              simp only [afterIndex]
              omega
        rw [← indexEq]
        exact rooted
  have supportedChildNonempty : ∀ {signature}
      (wire : Var structuralOuter signature),
      supportedPending.incidencePaths wire.index.val ≠ [] ↔
        childPending.incidencePaths wire.index.val ≠ [] := by
    intro signature wire
    let commonWire := wire.appendLeft oldLocals
    have inherited := childSourceNonempty commonWire
    rw [Region.incidencePaths_ofItems, Region.incidencePaths_ofItems]
      at inherited
    change supportedItems.incidencePaths wire.index.val 0 ≠ [] ↔
      childItems.incidencePaths wire.index.val 0 ≠ []
    simpa [frame, commonWire, oldLocals, pendingLocals,
      Content.Cut.rootFrame, Transform.Frame.replace,
      Transform.Frame.keep, Transform.Frame.localKeep] using inherited
  have childPendingValidity := filledValidityOfReplacement
    request.occurrence.interface request.occurrence.context
    supportedPending childPending supportedValidity.1 supportedValidity.2
    childLocalCanonical supportedChildNonempty
  have recursiveSourceCanonical :
      (request.occurrence.context.fill
        (polaritySource request.polarity recursiveInstantiated
          childPending)).Canonical :=
    polaritySource_property request.polarity
      (fun region => (request.occurrence.context.fill region).Canonical)
      recursiveInstantiated childPending recursiveValidity.1
      childPendingValidity.1
  have recursiveSourceExternal : OpenDiagram.ExternalTwoEnded
      request.occurrence.interface.boundaryWire
      (request.occurrence.context.fill
        (polaritySource request.polarity recursiveInstantiated
          childPending)) :=
    polaritySource_property request.polarity
      (fun region => OpenDiagram.ExternalTwoEnded
        request.occurrence.interface.boundaryWire
        (request.occurrence.context.fill region))
      recursiveInstantiated childPending recursiveValidity.2
      childPendingValidity.2
  let recursiveRequest : Telescope.Request recursiveInstantiated
      childPending := {
    boundary := request.boundary
    source := request.occurrence.interface.withBody
      (request.occurrence.context.fill
        (polaritySource request.polarity recursiveInstantiated
          childPending)) recursiveSourceCanonical recursiveSourceExternal
    endpoint := childPending
    polarity := request.polarity
    occurrence := exactOccurrence request.occurrence.interface
      request.occurrence.context
      (polaritySource request.polarity recursiveInstantiated childPending)
      recursiveSourceCanonical recursiveSourceExternal
    instantiatedCanonical := recursiveValidity.1
    instantiatedExternalTwoEnded := recursiveValidity.2
    pendingCanonical := childPendingValidity.1
    pendingExternalTwoEnded := childPendingValidity.2
    endpointCanonical := childPendingValidity.1
    endpointExternalTwoEnded := childPendingValidity.2
    continuation := Telescope.refl request.polarity
      request.occurrence.interface request.occurrence.context
      childPendingValidity.1 childPendingValidity.2 polarityEq
  }
  have childCompiled := bodyIH bodyCanonical
    (by simpa [frame, data, Content.Cut.rootFrame,
      Content.Cut.targetHead, Transform.Frame.replace] using childEvidence)
    recursiveRequest
  have bodyTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      recursiveInstantiated childPending recursiveValidity.1
      recursiveValidity.2 childPendingValidity.1 childPendingValidity.2 := by
    exact Telescope.StrictDerives.toTelescope request.polarity
      request.occurrence.interface request.occurrence.context
      recursiveValidity.1 recursiveValidity.2 childPendingValidity.1
      childPendingValidity.2 polarityEq
      (by simpa only [recursiveRequest, Telescope.Request.Result] using
        childCompiled)
  have preparationTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      fullInstantiated childPending
      (by simpa only [fullInstantiated, oldLocals] using
        request.instantiatedCanonical)
      (by
        intro signature wire
        simpa only [fullInstantiated, oldLocals] using
          request.instantiatedExternalTwoEnded wire)
      childPendingValidity.1 childPendingValidity.2 :=
    telescopeTrans resultBridgeTelescope bodyTelescope
  have pendingSupportHosted : HostedStrict originalPending
      supportedPending := by
    have materialHosted := cutSupportedRootItemsHosted oldLocals rootRename items
    have lifted := HostedStrict.adjoinAt pendingLocals
      (Region.ofItems items) (Region.ofItems supportedItems)
      (by simpa only [rootRename, supportedItems] using materialHosted)
    exact HostedStrict.iso
      (RegionIso.adjoinAtOfItems pendingLocals items).symm
      (RegionIso.adjoinAtOfItems pendingLocals supportedItems) lifted
  have cleanupTelescope : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      supportedPending originalPending supportedValidity.1 supportedValidity.2
      (by simpa only [originalPending, pendingLocals] using
        request.pendingCanonical)
      (by
        intro signature wire
        simpa only [originalPending, pendingLocals] using
          request.pendingExternalTwoEnded wire) :=
    telescopeOfHostedExact pendingSupportHosted.symm request.polarity
      request.occurrence.interface request.occurrence.context
      supportedValidity.1 supportedValidity.2
      (by simpa only [originalPending, pendingLocals] using
        request.pendingCanonical)
      (by
        intro signature wire
        simpa only [originalPending, pendingLocals] using
          request.pendingExternalTwoEnded wire)
      polarityEq
  have supportedContinuation : Telescope request.polarity
      request.occurrence.interface request.occurrence.context
      supportedPending request.endpoint supportedValidity.1 supportedValidity.2
      request.endpointCanonical request.endpointExternalTwoEnded := by
    apply telescopeTrans cleanupTelescope
    simpa only [originalPending, pendingLocals] using request.continuation
  let supportedRequest : Telescope.Request fullInstantiated
      supportedPending := {
    boundary := request.boundary
    source := request.source
    endpoint := request.endpoint
    polarity := request.polarity
    occurrence := request.occurrence
    instantiatedCanonical := by
      simpa only [fullInstantiated, oldLocals] using
        request.instantiatedCanonical
    instantiatedExternalTwoEnded := by
      intro signature wire
      simpa only [fullInstantiated, oldLocals] using
        request.instantiatedExternalTwoEnded wire
    pendingCanonical := supportedValidity.1
    pendingExternalTwoEnded := supportedValidity.2
    endpointCanonical := request.endpointCanonical
    endpointExternalTwoEnded := request.endpointExternalTwoEnded
    continuation := supportedContinuation
  }
  let description : Content.Cut.Wrap.Description structuralOuter := {
    arguments := wires
    before := structuralBefore
    after := structuralAfter
    items := supportedItems
    itemsEdit := edit
  }
  let preparedIso : RegionIso (WireEquiv.refl structuralOuter)
      childPending description.target :=
    (RegionIso.adjoinAtOfItems pendingLocals childItems).symm.trans
      (RegionIso.adjoinAt pendingLocals .nil childIso.symm)
  have rawPreparedValidity := filledValidityOfScope
    supportedRequest.occurrence.interface supportedRequest.occurrence.context
    childPending description.target childPendingValidity.1
    childPendingValidity.2 (ScopePreservation.ofIso preparedIso)
  have pendingEq : supportedPending = description.source := by
    rfl
  let branch : supportedRequest.Branch childPending := {
    rawPrepared := description.target
    rawPending := description.source
    localRule := symmetric Content.Cut.Local
    inject := fun step => Step.cutShape step
    preparedCanonical := childPendingValidity.1
    preparedExternalTwoEnded := childPendingValidity.2
    rawPreparedCanonical := rawPreparedValidity.1
    rawPreparedExternalTwoEnded := rawPreparedValidity.2
    rawPendingCanonical := by
      rw [← pendingEq]
      exact supportedValidity.1
    rawPendingExternalTwoEnded := by
      intro signature wire
      rw [← pendingEq]
      exact supportedValidity.2 wire
    preparedIso := preparedIso
    pendingIso := RegionIso.ofEq pendingEq
    localStep := Or.inr (.wrap (.mk description))
    preparation := preparationTelescope
  }
  exact branch.derive

end Structural

end VisualProof.Rule.Completeness.Comprehension
