import VisualProof.Diagram.Semantics.Algebra
import VisualProof.Diagram.Semantics.OpenIsomorphism
import VisualProof.Diagram.Semantics.ScopedRewrite
import VisualProof.Rule.Lambda.HeadStrip

namespace VisualProof.Rule.Lambda.HeadStrip

open Diagram
open Theory
open VisualProof.Data.Finite

private theorem Values.exists_append
    (values : Values model (left ++ right)) :
    ∃ (leftValues : Values model left) (rightValues : Values model right),
      leftValues.append rightValues = values := by
  induction left with
  | nil => exact ⟨PUnit.unit, values, rfl⟩
  | cons signature rest induction =>
      rcases values with ⟨head, tail⟩
      rcases induction tail with ⟨leftValues, rightValues, equality⟩
      exact ⟨(head, leftValues), rightValues, congrArg (Prod.mk head) equality⟩

private def Values.repeatedIota (model : Model) : {count : Nat} →
    (Fin count → model.Carrier) →
    Values model (List.replicate count Sig.iota)
  | 0, _ => PUnit.unit
  | _ + 1, values =>
      (values 0, Values.repeatedIota model fun position => values position.succ)

private def Values.singletonIota (model : Model) (value : model.Carrier) :
    Values model [Sig.iota] :=
  (value, PUnit.unit)

@[simp] private theorem Values.lookup_repeatedIota
    (values : Fin count → model.Carrier) (position : Fin count) :
    (Values.repeatedIota model values).lookup
      (Identification.Repeated.wire .iota position) = values position := by
  induction count with
  | zero => exact Fin.elim0 position
  | succ count induction =>
      refine Fin.cases rfl (fun rest => ?_) position
      exact induction (fun position => values position.succ) rest

private theorem ItemSeq.denote_ofList
    (model : Model) (environment : Values model wires)
    (items : List (Item wires)) :
    denoteItemSeq model environment (ItemSeq.ofList items) ↔
      ∀ item, item ∈ items → denoteItem model environment item := by
  induction items with
  | nil => simp [ItemSeq.ofList]
  | cons head tail induction =>
      simp only [ItemSeq.ofList, denoteItemSeq_cons, List.mem_cons]
      constructor
      · rintro ⟨headDenotes, tailDenotes⟩ item (rfl | member)
        · exact headDenotes
        · exact induction.mp tailDenotes item member
      · intro all
        exact ⟨all head (Or.inl rfl), induction.mpr fun item member =>
          all item (Or.inr member)⟩

private theorem retainedLookup
    (description : Description outer) (model : Model)
    (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (freshEnv : Values model
      (List.replicate description.argumentIndices.length .iota))
    (wire : Var (outer ++ description.locals) signature) :
    (outerEnv.append (localEnv.append freshEnv)).lookup
        (description.targetRetain wire) =
      (outerEnv.append localEnv).lookup wire := by
  apply Var.appendCases (left := outer) (right := description.locals)
    (motive := fun wire =>
      (outerEnv.append (localEnv.append freshEnv)).lookup
          (description.targetRetain wire) =
        (outerEnv.append localEnv).lookup wire)
  · intro inheritedSignature inherited
    simp [Description.targetRetain, Region.adjoinHostWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [Description.targetRetain, Region.adjoinHostWire,
      Region.conjoinLeftWire]

private theorem targetRetainedEnvironment
    (description : Description outer) (model : Model)
    (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (freshEnv : Values model
      (List.replicate description.argumentIndices.length .iota)) :
    Values.rename description.targetRetain
        (outerEnv.append (localEnv.append freshEnv)) =
      outerEnv.append localEnv := by
  apply Values.ext
  intro signature wire
  simpa only [Values.lookup_rename] using
    retainedLookup description model outerEnv localEnv freshEnv wire

private theorem sourceRetainedLookup
    (description : Description outer) (model : Model)
    (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (equationValue : model.Carrier)
    (wire : Var (outer ++ description.locals) signature) :
    (outerEnv.append (localEnv.append
      (Values.singletonIota model equationValue))).lookup
        (description.sourceRetain wire) =
      (outerEnv.append localEnv).lookup wire := by
  apply Var.appendCases (left := outer) (right := description.locals)
    (motive := fun wire =>
      (outerEnv.append (localEnv.append
        (Values.singletonIota model equationValue))).lookup
          (description.sourceRetain wire) =
        (outerEnv.append localEnv).lookup wire)
  · intro inheritedSignature inherited
    simp [Description.sourceRetain, Region.adjoinHostWire,
      Region.conjoinLeftWire]
  · intro localSignature localWire
    simp [Description.sourceRetain, Region.adjoinHostWire,
      Region.conjoinLeftWire]

private theorem sourceRetainedEnvironment
    (description : Description outer) (model : Model)
    (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (equationValue : model.Carrier) :
    Values.rename description.sourceRetain
        (outerEnv.append (localEnv.append
          (Values.singletonIota model equationValue))) =
      outerEnv.append localEnv := by
  apply Values.ext
  intro signature wire
  simpa only [Values.lookup_rename] using
    sourceRetainedLookup description model outerEnv localEnv equationValue wire

private theorem equationLookup
    (description : Description outer) (model : Model)
    (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (equationValue : model.Carrier) :
    (outerEnv.append (localEnv.append
      (Values.singletonIota model equationValue))).lookup
        description.equation = equationValue := by
  simp only [Description.equation, Values.lookup_append_right,
    Values.singletonIota]
  rfl

private theorem argumentWireLookup
    (description : Description outer) (model : Model)
    (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (values : Fin description.argumentIndices.length → model.Carrier)
    (position : Fin description.argumentIndices.length) :
    (outerEnv.append (localEnv.append
      (Values.repeatedIota model values))).lookup
        (description.argumentWire position) = values position := by
  simp [Description.argumentWire, Identification.freshLocalWire]

private theorem eval_eq_of_support_agree
    (model : Model) (term : VisualProof.Lambda.Term 0 (Fin arity))
    (left right : Fin arity → model.Carrier)
    (agree : ∀ slot, slot ∈ term.freeSupport → left slot = right slot) :
    model.eval term left = model.eval term right := by
  have leftMapped := model.eval_mapFree term.freeSupport.get term.compact left
  have rightMapped := model.eval_mapFree term.freeSupport.get term.compact right
  rw [term.compact_reconstruct] at leftMapped rightMapped
  rw [leftMapped, rightMapped]
  apply congrArg (model.eval term.compact)
  funext position
  exact agree (term.freeSupport.get position) (List.get_mem ..)

private theorem compactionEvaluation
    (model : Model)
    (commonTerm : VisualProof.Lambda.Term 0 (Fin commonArity))
    (commonPorts : Fin commonArity → Var wires .iota)
    (physicalTerm : VisualProof.Lambda.Term 0 (Var wires .iota))
    (evidence : PhysicalCompaction commonTerm commonPorts physicalTerm)
    (environment : Values model wires) :
    model.eval physicalTerm.compact (fun position =>
        environment.lookup (physicalTerm.freeSupport.get position)) =
      model.eval commonTerm (fun slot =>
        environment.lookup (commonPorts slot)) := by
  cases evidence with
  | empty closed commonEq compactEq =>
      rw [commonEq, compactEq]
      let closedZero : VisualProof.Lambda.Term 0 (Fin 0) :=
        closed.mapFree Empty.elim
      have physicalEvaluation := model.eval_mapFree
        (Fin.elim0 : Fin 0 → Fin physicalTerm.freeSupport.length)
        closedZero (fun position =>
          environment.lookup (physicalTerm.freeSupport.get position))
      have commonEvaluation := model.eval_mapFree
        (Fin.elim0 : Fin 0 → Fin commonArity) closedZero
        (fun slot => environment.lookup (commonPorts slot))
      have emptyPhysical :
          (Fin.elim0 : Fin 0 → Fin physicalTerm.freeSupport.length) ∘
              (Empty.elim : Empty → Fin 0) =
            (Empty.elim : Empty → Fin physicalTerm.freeSupport.length) := by
        funext impossible
        exact Empty.elim impossible
      have emptyCommon :
          (Fin.elim0 : Fin 0 → Fin commonArity) ∘
              (Empty.elim : Empty → Fin 0) =
            (Empty.elim : Empty → Fin commonArity) := by
        funext impossible
        exact Empty.elim impossible
      rw [VisualProof.Lambda.Term.mapFree_comp, emptyPhysical] at physicalEvaluation
      rw [VisualProof.Lambda.Term.mapFree_comp, emptyCommon] at commonEvaluation
      have physicalZeroEnvironment :
          ((fun position => environment.lookup
            (physicalTerm.freeSupport.get position)) ∘
              (Fin.elim0 : Fin 0 → Fin physicalTerm.freeSupport.length)) =
            (Fin.elim0 : Fin 0 → model.Carrier) := by
        funext impossible
        exact Fin.elim0 impossible
      have commonZeroEnvironment :
          ((fun position => environment.lookup (commonPorts position)) ∘
              (Fin.elim0 : Fin 0 → Fin commonArity)) =
            (Fin.elim0 : Fin 0 → model.Carrier) := by
        funext impossible
        exact Fin.elim0 impossible
      calc
        _ = model.eval closedZero
              ((fun position => environment.lookup
                (physicalTerm.freeSupport.get position)) ∘ Fin.elim0) :=
          physicalEvaluation
        _ = model.eval closedZero Fin.elim0 :=
          congrArg (model.eval closedZero) physicalZeroEnvironment
        _ = model.eval closedZero
              ((fun slot => environment.lookup (commonPorts slot)) ∘
                Fin.elim0) :=
          congrArg (model.eval closedZero) commonZeroEnvironment.symm
        _ = _ := commonEvaluation.symm
  | supported rename compactEq portsEq =>
      rw [compactEq]
      rw [model.eval_mapFree]
      apply eval_eq_of_support_agree model commonTerm
      intro slot member
      simp only [Function.comp_apply]
      rw [portsEq slot member]

private def commonEnvironment
    (description : Description outer) (model : Model)
    (baseEnv : Values model (outer ++ description.locals)) :
    Fin description.correspondence.commonArity → model.Carrier :=
  fun position => baseEnv.lookup (description.carrier position)

private theorem leftArgumentEvaluation
    (description : Description outer) (model : Model)
    (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (freshEnv : Values model
      (List.replicate description.argumentIndices.length .iota))
    (position : Fin description.argumentIndices.length) :
    let targetEnv := outerEnv.append (localEnv.append freshEnv)
    let baseEnv := outerEnv.append localEnv
    let index := description.argumentIndices.get position
    let physical := description.leftPhysicalArgument index
    model.eval physical.compact
        (fun slot => targetEnv.lookup
          (description.targetRetain (physical.freeSupport.get slot))) =
      model.eval (description.leftCommonArgument index)
        (commonEnvironment description model baseEnv) := by
  dsimp only
  let physical := description.leftPhysicalArgument
    (description.argumentIndices.get position)
  calc
    model.eval physical.compact (fun slot =>
        (outerEnv.append (localEnv.append freshEnv)).lookup
          (description.targetRetain (physical.freeSupport.get slot))) =
      model.eval (description.leftCommonArgument
        (description.argumentIndices.get position))
        (commonEnvironment description model
          (outerEnv.append localEnv)) := by
        rw [show (fun slot =>
          (outerEnv.append (localEnv.append freshEnv)).lookup
            (description.targetRetain (physical.freeSupport.get slot))) =
          (fun slot => (outerEnv.append localEnv).lookup
            (physical.freeSupport.get slot)) by
              funext slot
              exact retainedLookup description model outerEnv localEnv
                freshEnv (physical.freeSupport.get slot)]
        exact compactionEvaluation model
          (description.leftCommonArgument
            (description.argumentIndices.get position)) description.carrier
          physical (description.leftCompaction
            (description.argumentIndices.get position))
          (outerEnv.append localEnv)

private theorem rightArgumentEvaluation
    (description : Description outer) (model : Model)
    (outerEnv : Values model outer)
    (localEnv : Values model description.locals)
    (freshEnv : Values model
      (List.replicate description.argumentIndices.length .iota))
    (position : Fin description.argumentIndices.length) :
    let targetEnv := outerEnv.append (localEnv.append freshEnv)
    let baseEnv := outerEnv.append localEnv
    let index := description.argumentIndices.get position
    let physical := description.rightPhysicalArgument index
    model.eval physical.compact
        (fun slot => targetEnv.lookup
          (description.targetRetain (physical.freeSupport.get slot))) =
      model.eval (description.rightCommonArgument index)
        (commonEnvironment description model baseEnv) := by
  dsimp only
  let physical := description.rightPhysicalArgument
    (description.argumentIndices.get position)
  calc
    model.eval physical.compact (fun slot =>
        (outerEnv.append (localEnv.append freshEnv)).lookup
          (description.targetRetain (physical.freeSupport.get slot))) =
      model.eval (description.rightCommonArgument
        (description.argumentIndices.get position))
        (commonEnvironment description model
          (outerEnv.append localEnv)) := by
        rw [show (fun slot =>
          (outerEnv.append (localEnv.append freshEnv)).lookup
            (description.targetRetain (physical.freeSupport.get slot))) =
          (fun slot => (outerEnv.append localEnv).lookup
            (physical.freeSupport.get slot)) by
              funext slot
              exact retainedLookup description model outerEnv localEnv
                freshEnv (physical.freeSupport.get slot)]
        exact compactionEvaluation model
          (description.rightCommonArgument
            (description.argumentIndices.get position)) description.carrier
          physical (description.rightCompaction
            (description.argumentIndices.get position))
          (outerEnv.append localEnv)

private theorem commonArguments_of_wholeEquality
    (description : Description outer) (model : Model)
    (environment : Fin description.correspondence.commonArity →
      model.Carrier)
    (wholeEquality :
      model.eval
          (description.leftTerm.mapFree
            description.correspondence.left) environment =
        model.eval
          (description.rightTerm.mapFree
            description.correspondence.right) environment) :
    ∀ index,
      model.eval (description.leftCommonArgument index) environment =
        model.eval (description.rightCommonArgument index) environment := by
  intro index
  let leftMapped := description.leftSpine.mapFree
    description.correspondence.left
  let rightMapped := description.rightSpine.mapFree
    description.correspondence.right
  have leftShape : VisualProof.Lambda.headSpine
      (description.leftTerm.mapFree description.correspondence.left) =
        some leftMapped := by
    exact VisualProof.Lambda.headSpine_mapFree
      description.leftSpine_eq description.correspondence.left
  have rightShape : VisualProof.Lambda.headSpine
      (description.rightTerm.mapFree description.correspondence.right) =
        some rightMapped := by
    exact VisualProof.Lambda.headSpine_mapFree
      description.rightSpine_eq description.correspondence.right
  have leftHeadMapped : leftMapped.head =
      .bound description.headIndex := by
    simp [leftMapped, VisualProof.Lambda.HeadSpine.mapFree,
      description.leftHead, VisualProof.Lambda.Head.mapFree]
  have rightHeadMapped : rightMapped.head =
      .bound (Fin.cast description.sameBinders description.headIndex) := by
    simp [rightMapped, VisualProof.Lambda.HeadSpine.mapFree,
      description.rightHead, VisualProof.Lambda.Head.mapFree]
  have sameMappedArgumentCount : leftMapped.args.length =
      rightMapped.args.length := by
    simpa [leftMapped, rightMapped,
      VisualProof.Lambda.HeadSpine.mapFree] using
        description.sameArgumentCount
  have mappedValid : index.val < leftMapped.args.length := by
    simp [leftMapped, VisualProof.Lambda.HeadSpine.mapFree]
  have reflected := model.rigidHead_args_reflect leftShape rightShape
    description.sameBinders description.headIndex leftHeadMapped
    rightHeadMapped sameMappedArgumentCount environment
    wholeEquality index.val mappedValid
  simpa [leftMapped, rightMapped, Description.leftCommonArgument,
    Description.rightCommonArgument, Description.leftArgument,
    Description.rightArgument,
    VisualProof.Lambda.HeadSpine.mapFree,
    VisualProof.Lambda.prefixClose_mapFree] using reflected

private theorem rigidSkeletonEvaluation_eq
    (model : Model)
    {leftBinders rightBinders leftCount rightCount : Nat}
    (sameBinders : leftBinders = rightBinders)
    (headIndex : Fin leftBinders)
    (sameCount : leftCount = rightCount)
    (leftValues : Fin leftCount → model.Carrier)
    (rightValues : Fin rightCount → model.Carrier)
    (valuesEqual : ∀ index,
      leftValues index = rightValues (Fin.cast sameCount index)) :
    model.eval
        (VisualProof.Lambda.rigidBoundSkeleton leftBinders headIndex leftCount)
        leftValues =
      model.eval
        (VisualProof.Lambda.rigidBoundSkeleton rightBinders
          (Fin.cast sameBinders headIndex) rightCount) rightValues := by
  subst rightBinders
  subst rightCount
  have environmentsEqual : leftValues = rightValues := by
    funext index
    exact valuesEqual index
  subst rightValues
  rfl

private theorem wholeEquality_of_commonArguments
    (description : Description outer) (model : Model)
    (environment : Fin description.correspondence.commonArity →
      model.Carrier)
    (argumentsEqual : ∀ index,
      model.eval (description.leftCommonArgument index) environment =
        model.eval (description.rightCommonArgument index) environment) :
    model.eval
        (description.leftTerm.mapFree description.correspondence.left)
        environment =
      model.eval
        (description.rightTerm.mapFree description.correspondence.right)
        environment := by
  let leftMapped := description.leftSpine.mapFree
    description.correspondence.left
  let rightMapped := description.rightSpine.mapFree
    description.correspondence.right
  have leftShape : VisualProof.Lambda.headSpine
      (description.leftTerm.mapFree description.correspondence.left) =
        some leftMapped :=
    VisualProof.Lambda.headSpine_mapFree description.leftSpine_eq _
  have rightShape : VisualProof.Lambda.headSpine
      (description.rightTerm.mapFree description.correspondence.right) =
        some rightMapped :=
    VisualProof.Lambda.headSpine_mapFree description.rightSpine_eq _
  have leftHeadMapped : leftMapped.head =
      .bound description.headIndex := by
    simp [leftMapped, VisualProof.Lambda.HeadSpine.mapFree,
      description.leftHead, VisualProof.Lambda.Head.mapFree]
  have rightHeadMapped : rightMapped.head =
      .bound (Fin.cast description.sameBinders description.headIndex) := by
    simp [rightMapped, VisualProof.Lambda.HeadSpine.mapFree,
      description.rightHead, VisualProof.Lambda.Head.mapFree]
  have sameMappedCount : leftMapped.args.length =
      rightMapped.args.length := by
    simpa [leftMapped, rightMapped,
      VisualProof.Lambda.HeadSpine.mapFree] using
        description.sameArgumentCount
  have leftRebuild := VisualProof.Lambda.rigidBoundSkeleton_bind_arguments
    leftShape description.headIndex leftHeadMapped
  have rightRebuild := VisualProof.Lambda.rigidBoundSkeleton_bind_arguments
    rightShape (Fin.cast description.sameBinders description.headIndex)
      rightHeadMapped
  let leftValues : Fin leftMapped.args.length → model.Carrier :=
    fun index => model.eval
      (VisualProof.Lambda.prefixClose leftMapped.binders
        (leftMapped.args.get index)) environment
  let rightValues : Fin rightMapped.args.length → model.Carrier :=
    fun index => model.eval
      (VisualProof.Lambda.prefixClose rightMapped.binders
        (rightMapped.args.get index)) environment
  have mappedValuesEqual : ∀ index,
      leftValues index = rightValues (Fin.cast sameMappedCount index) := by
    intro index
    have originalValid : index.val < description.leftSpine.args.length := by
      simpa [leftMapped, VisualProof.Lambda.HeadSpine.mapFree] using index.isLt
    let originalIndex : Fin description.leftSpine.args.length :=
      ⟨index.val, originalValid⟩
    simpa [leftValues, rightValues, leftMapped, rightMapped,
      Description.leftCommonArgument, Description.rightCommonArgument,
      Description.leftArgument, Description.rightArgument,
      VisualProof.Lambda.HeadSpine.mapFree,
      VisualProof.Lambda.prefixClose_mapFree, originalIndex] using
        argumentsEqual originalIndex
  have middleEquality := rigidSkeletonEvaluation_eq model
    description.sameBinders description.headIndex sameMappedCount
    leftValues rightValues mappedValuesEqual
  calc
    model.eval
        (description.leftTerm.mapFree description.correspondence.left)
        environment =
      model.eval
        ((VisualProof.Lambda.rigidBoundSkeleton leftMapped.binders
          description.headIndex leftMapped.args.length).bindFree
            (fun index => VisualProof.Lambda.prefixClose leftMapped.binders
              (leftMapped.args.get index))) environment :=
        (model.betaEta_sound leftRebuild).symm
    _ = model.eval
        (VisualProof.Lambda.rigidBoundSkeleton leftMapped.binders
          description.headIndex leftMapped.args.length) leftValues := by
      simpa [leftValues] using model.eval_bindFree
        (VisualProof.Lambda.rigidBoundSkeleton leftMapped.binders
          description.headIndex leftMapped.args.length)
        (fun index => VisualProof.Lambda.prefixClose leftMapped.binders
          (leftMapped.args.get index)) environment
    _ = model.eval
        (VisualProof.Lambda.rigidBoundSkeleton rightMapped.binders
          (Fin.cast description.sameBinders description.headIndex)
          rightMapped.args.length) rightValues := middleEquality
    _ = model.eval
        ((VisualProof.Lambda.rigidBoundSkeleton rightMapped.binders
          (Fin.cast description.sameBinders description.headIndex)
          rightMapped.args.length).bindFree
            (fun index => VisualProof.Lambda.prefixClose rightMapped.binders
              (rightMapped.args.get index))) environment := by
      symm
      simpa [rightValues] using model.eval_bindFree
        (VisualProof.Lambda.rigidBoundSkeleton rightMapped.binders
          (Fin.cast description.sameBinders description.headIndex)
          rightMapped.args.length)
        (fun index => VisualProof.Lambda.prefixClose rightMapped.binders
          (rightMapped.args.get index)) environment
    _ = model.eval
        (description.rightTerm.mapFree description.correspondence.right)
        environment := model.betaEta_sound rightRebuild

private theorem argumentItems_denotes_of
    (description : Description outer) (model : Model)
    (environment : Values model
      (outer ++ (description.locals ++
        List.replicate description.argumentIndices.length .iota)))
    (all : ∀ position,
      denoteItem model environment (description.leftArgumentItem position) ∧
        denoteItem model environment
          (description.rightArgumentItem position)) :
    denoteItemSeq model environment description.argumentItems := by
  rw [Description.argumentItems, ItemSeq.denote_ofList]
  intro item member
  rcases List.mem_flatten.mp member with ⟨pair, pairMember, itemMember⟩
  rcases List.get_of_mem pairMember with ⟨position, pairEq⟩
  let index : Fin description.argumentIndices.length :=
    ⟨position.val, by simpa using position.isLt⟩
  have pairEq' : [description.leftArgumentItem index,
      description.rightArgumentItem index] = pair := by
    simpa [index] using pairEq
  rw [← pairEq'] at itemMember
  simp only [List.mem_cons] at itemMember
  rcases itemMember with itemEq | itemMember
  · subst item
    exact (all index).1
  · rcases itemMember with itemEq | impossible
    · subst item
      exact (all index).2
    · exact nomatch impossible

private theorem argumentItems_denotes_at
    (description : Description outer) (model : Model)
    (environment : Values model
      (outer ++ (description.locals ++
        List.replicate description.argumentIndices.length .iota)))
    (denotes : denoteItemSeq model environment description.argumentItems)
    (position : Fin description.argumentIndices.length) :
    denoteItem model environment (description.leftArgumentItem position) ∧
      denoteItem model environment
        (description.rightArgumentItem position) := by
  rw [Description.argumentItems, ItemSeq.denote_ofList] at denotes
  have pairMember : [description.leftArgumentItem position,
      description.rightArgumentItem position] ∈
      List.ofFn (fun position => [
        description.leftArgumentItem position,
        description.rightArgumentItem position]) := by
    let listPosition : Fin (List.ofFn (fun position => [
        description.leftArgumentItem position,
        description.rightArgumentItem position])).length :=
      ⟨position.val, by simp⟩
    simpa [listPosition] using List.get_mem
      (List.ofFn (fun position => [
        description.leftArgumentItem position,
        description.rightArgumentItem position])) listPosition
  constructor
  · apply denotes (description.leftArgumentItem position)
    apply List.mem_flatten.mpr
    exact ⟨_, pairMember, by simp⟩
  · apply denotes (description.rightArgumentItem position)
    apply List.mem_flatten.mpr
    exact ⟨_, pairMember, by simp⟩

theorem Local.sound_iff {before after : Region outer}
    (step : Local before after) (model : Model)
    (outerEnv : Values model outer) :
    denoteRegion model outerEnv before ↔
      denoteRegion model outerEnv after := by
  cases step with
  | strip description =>
      simp only [Description.source, Description.target, denoteRegion_mk]
      constructor
      · rintro ⟨expandedLocal, sourceDenotes⟩
        rcases Values.exists_append (left := description.locals)
          (right := [Sig.iota]) expandedLocal with
          ⟨localEnv, equationEnv, expandedEq⟩
        rcases equationEnv with ⟨equationValue, unitValue⟩
        cases unitValue
        subst expandedLocal
        rcases sourceDenotes with
          ⟨leftDenotes, rightDenotes, sourceRestDenotes⟩
        let baseEnv := outerEnv.append localEnv
        let commonEnv := commonEnvironment description model baseEnv
        have nativeEquality :
            model.eval description.leftTerm
                (fun slot => baseEnv.lookup (description.leftPorts slot)) =
              model.eval description.rightTerm
                (fun slot => baseEnv.lookup
                  (description.rightPorts slot)) := by
          simp only [denoteItem_term] at leftDenotes rightDenotes
          have leftPortsRetained : (fun slot =>
              (outerEnv.append (localEnv.append
                (Values.singletonIota model equationValue))).lookup
                (description.sourceRetain (description.leftPorts slot))) =
              (fun slot => baseEnv.lookup
                (description.leftPorts slot)) := by
            funext slot
            exact sourceRetainedLookup description model outerEnv localEnv
              equationValue (description.leftPorts slot)
          have rightPortsRetained : (fun slot =>
              (outerEnv.append (localEnv.append
                (Values.singletonIota model equationValue))).lookup
                (description.sourceRetain (description.rightPorts slot))) =
              (fun slot => baseEnv.lookup
                (description.rightPorts slot)) := by
            funext slot
            exact sourceRetainedLookup description model outerEnv localEnv
              equationValue (description.rightPorts slot)
          have leftEvalEq := congrArg (model.eval description.leftTerm)
            leftPortsRetained
          have rightEvalEq := congrArg (model.eval description.rightTerm)
            rightPortsRetained
          exact leftEvalEq.symm.trans
            (leftDenotes.symm.trans (rightDenotes.trans rightEvalEq))
        have mappedEquality :
            model.eval
                (description.leftTerm.mapFree
                  description.correspondence.left) commonEnv =
              model.eval
                (description.rightTerm.mapFree
                  description.correspondence.right) commonEnv := by
          rw [model.eval_mapFree, model.eval_mapFree]
          simpa [commonEnv, commonEnvironment,
            Description.leftPorts, Description.rightPorts,
            Function.comp_def] using nativeEquality
        have argumentsEqual := commonArguments_of_wholeEquality description
          model commonEnv mappedEquality
        let freshEnv : Values model
            (List.replicate description.argumentIndices.length .iota) :=
          Values.repeatedIota model fun position =>
            model.eval (description.leftCommonArgument
              (description.argumentIndices.get position)) commonEnv
        refine ⟨localEnv.append freshEnv, ?_⟩
        rw [denoteItemSeq_append]
        constructor
        · apply argumentItems_denotes_of description model
          intro position
          constructor
          · simp only [Description.leftArgumentItem, denoteItem_term]
            rw [argumentWireLookup description model outerEnv localEnv]
            exact (leftArgumentEvaluation description model outerEnv localEnv
              freshEnv position).symm
          · simp only [Description.rightArgumentItem, denoteItem_term]
            rw [argumentWireLookup description model outerEnv localEnv]
            exact (argumentsEqual (description.argumentIndices.get position)).trans
              (rightArgumentEvaluation description model outerEnv localEnv
                freshEnv position).symm
        · have sourceRenamed := denoteItemSeq_renameWires model
            description.sourceRetain
            (outerEnv.append (localEnv.append
              (Values.singletonIota model equationValue))) description.rest
          rw [sourceRetainedEnvironment description model outerEnv localEnv
            equationValue] at sourceRenamed
          have baseRest := sourceRenamed.mp sourceRestDenotes
          have targetRenamed := denoteItemSeq_renameWires model
            description.targetRetain
            (outerEnv.append (localEnv.append freshEnv)) description.rest
          rw [targetRetainedEnvironment description model outerEnv localEnv
            freshEnv] at targetRenamed
          exact targetRenamed.mpr baseRest
      · rintro ⟨expandedLocal, targetDenotes⟩
        rcases Values.exists_append (left := description.locals)
          (right := List.replicate description.argumentIndices.length .iota)
          expandedLocal with ⟨localEnv, freshEnv, expandedEq⟩
        subst expandedLocal
        rw [denoteItemSeq_append] at targetDenotes
        rcases targetDenotes with ⟨argumentDenotes, targetRestDenotes⟩
        let baseEnv := outerEnv.append localEnv
        let commonEnv := commonEnvironment description model baseEnv
        have argumentsEqual : ∀ index,
            model.eval (description.leftCommonArgument index) commonEnv =
              model.eval (description.rightCommonArgument index) commonEnv := by
          intro index
          classical
          by_cases sameArgument : description.leftCommonArgument index =
              description.rightCommonArgument index
          · rw [sameArgument]
          · have member : index ∈ description.argumentIndices := by
              rw [Description.argumentIndices, mem_filterFin]
              simp [sameArgument]
            rcases List.get_of_mem member with ⟨position, selectedEq⟩
            have selectedDenotes := argumentItems_denotes_at description model
              (outerEnv.append (localEnv.append freshEnv)) argumentDenotes
              position
            rcases selectedDenotes with ⟨leftDenotes, rightDenotes⟩
            simp only [Description.leftArgumentItem, denoteItem_term] at leftDenotes
            simp only [Description.rightArgumentItem, denoteItem_term] at rightDenotes
            have selectedArgumentEquality :
                model.eval (description.leftCommonArgument
                    (description.argumentIndices.get position)) commonEnv =
                  model.eval (description.rightCommonArgument
                    (description.argumentIndices.get position)) commonEnv :=
              (leftArgumentEvaluation description model outerEnv localEnv
                  freshEnv position).symm.trans
                (leftDenotes.symm.trans
                  (rightDenotes.trans
                    (rightArgumentEvaluation description model outerEnv
                      localEnv freshEnv position)))
            simpa only [selectedEq] using selectedArgumentEquality
        have mappedEquality := wholeEquality_of_commonArguments description
          model commonEnv argumentsEqual
        have nativeEquality :
            model.eval description.leftTerm
                (fun slot => baseEnv.lookup (description.leftPorts slot)) =
              model.eval description.rightTerm
                (fun slot => baseEnv.lookup
                  (description.rightPorts slot)) := by
          rw [model.eval_mapFree, model.eval_mapFree] at mappedEquality
          simpa [commonEnv, commonEnvironment, Description.leftPorts,
            Description.rightPorts, Function.comp_def] using mappedEquality
        let equationValue := model.eval description.leftTerm
          (fun slot => baseEnv.lookup (description.leftPorts slot))
        refine ⟨localEnv.append
          (Values.singletonIota model equationValue), ?_⟩
        constructor
        · simp only [denoteItem_term]
          rw [show (outerEnv.append (localEnv.append
              (Values.singletonIota model equationValue))).lookup
                description.equation = equationValue by
            exact equationLookup description model outerEnv localEnv
              equationValue]
          rw [show (fun slot =>
              (outerEnv.append (localEnv.append
                (Values.singletonIota model equationValue))).lookup
                  (description.sourceRetain
                    (description.leftPorts slot))) =
              (fun slot => baseEnv.lookup
                (description.leftPorts slot)) by
            funext slot
            exact sourceRetainedLookup description model outerEnv localEnv
              equationValue (description.leftPorts slot)]
        · constructor
          · simp only [denoteItem_term]
            rw [show (outerEnv.append (localEnv.append
                (Values.singletonIota model equationValue))).lookup
                  description.equation = equationValue by
              exact equationLookup description model outerEnv localEnv
                equationValue]
            rw [show (fun slot =>
                (outerEnv.append (localEnv.append
                  (Values.singletonIota model equationValue))).lookup
                    (description.sourceRetain
                      (description.rightPorts slot))) =
                (fun slot => baseEnv.lookup
                  (description.rightPorts slot)) by
              funext slot
              exact sourceRetainedLookup description model outerEnv localEnv
                equationValue (description.rightPorts slot)]
            exact nativeEquality
          · have targetRenamed := denoteItemSeq_renameWires model
              description.targetRetain
              (outerEnv.append (localEnv.append freshEnv)) description.rest
            rw [targetRetainedEnvironment description model outerEnv localEnv
              freshEnv] at targetRenamed
            have baseRest := targetRenamed.mp targetRestDenotes
            have sourceRenamed := denoteItemSeq_renameWires model
              description.sourceRetain
              (outerEnv.append (localEnv.append
                (Values.singletonIota model equationValue))) description.rest
            rw [sourceRetainedEnvironment description model outerEnv localEnv
              equationValue] at sourceRenamed
            exact sourceRenamed.mpr baseRest

/-- Rigid bound-head stripping preserves denotation in both directions. -/
theorem sound {boundary : List Sig}
    {source target : OpenDiagram boundary}
    (step : VisualProof.Rule.Lambda.HeadStrip source target) :
    ∀ (model : Model) (args : Values model boundary),
      denoteOpen model source args ↔ denoteOpen model target args := by
  intro model args
  cases step with
  | strip canonicalSource description sourceIso targetIso =>
      rw [sourceIso.denoteOpen_iff model args,
        description.occurrence.host_iso.denoteOpen_iff model args]
      have bodyIff : ∀ environment,
          denoteRegion model environment
              (description.occurrence.context.fill description.primary.source) ↔
            denoteRegion model environment description.targetBody := by
        intro environment
        exact (description.occurrence.context.denote_fill_iff
          description.primary.source description.primary.target
          (fun siteEnv => Local.sound_iff (.strip description.primary)
            model siteEnv) environment).trans
              (description.completion.sound_iff model environment)
      exact (OpenDiagram.denote_body_iff bodyIff).trans
        (targetIso.denoteOpen_iff model args)

end VisualProof.Rule.Lambda.HeadStrip
