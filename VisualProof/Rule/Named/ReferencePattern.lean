import VisualProof.Rule.Comprehension
import VisualProof.Rule.NamedReference

namespace VisualProof.Rule

open VisualProof
open VisualProof.Data.Finite
open Diagram
open Theory

private theorem eraseDups_eq_self_of_nodup [BEq α] [LawfulBEq α] :
    ∀ (values : List α), values.Nodup → values.eraseDups = values
  | [], _ => rfl
  | head :: tail, hnodup => by
      rw [List.eraseDups_cons]
      have hparts := List.nodup_cons.mp hnodup
      have hfilter :
          tail.filter (fun value => !value == head) = tail := by
        apply List.filter_eq_self.mpr
        intro value hvalue
        have hne : value ≠ head := by
          intro equality
          rw [equality] at hvalue
          exact hparts.1 hvalue
        simpa [bne_iff_ne] using hne
      rw [hfilter, eraseDups_eq_self_of_nodup tail hparts.2]

private theorem length_allFin (n : Nat) : (allFin n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allFin, ih]

private theorem get_allFin (n : Nat) (index : Fin (allFin n).length) :
    (allFin n).get index = Fin.cast (length_allFin n) index := by
  apply Fin.ext
  simp [allFin_eq_finRange, List.get_eq_getElem, List.getElem_finRange]

private theorem namedReferencePattern_exposed
    (signature : List Nat) (definition : Fin signature.length) :
    (namedReferencePatternRaw signature definition).exposedWires =
      allFin (signature.get definition) := by
  unfold OpenConcreteDiagram.exposedWires
  change (allFin (signature.get definition)).eraseDups =
    allFin (signature.get definition)
  exact eraseDups_eq_self_of_nodup _
    (allFin_nodup (signature.get definition))

private theorem namedReferencePattern_hidden
    (signature : List Nat) (definition : Fin signature.length) :
    (namedReferencePatternRaw signature definition).hiddenWires = [] := by
  rw [OpenConcreteDiagram.hiddenWires,
    namedReferencePattern_exposed signature definition]
  simp only [namedReferencePatternRaw, ConcreteElaboration.exactScopeWires,
    List.filter_eq_nil_iff]
  intro wire _
  simp only [Bool.not_eq_true, decide_eq_false_iff_not]
  intro hnot
  exact hnot (mem_allFin wire)

private theorem namedReferencePattern_occurrences
    (signature : List Nat) (definition : Fin signature.length) :
    ConcreteElaboration.localOccurrences
        (namedReferencePatternRaw signature definition).diagram
        (namedReferencePatternRaw signature definition).diagram.root =
      [.node ⟨0, by simp [namedReferencePatternRaw]⟩] := by
  simp [namedReferencePatternRaw, ConcreteElaboration.localOccurrences,
    filterFin, allFin_eq_finRange, List.finRange_succ_last,
    CNode.region, CRegion.parent?]
  rfl

/-- The intrinsic relation variable referenced by the canonical one-node
pattern. -/
def namedReferenceRelation (signature : List Nat)
    (definition : Fin signature.length) :
    NamedRel signature (signature.get definition) where
  index := definition
  hasArity := rfl

/-- The canonical one-node concrete pattern denotes exactly its named
relation applied to the ordered external arguments. -/
theorem namedReferencePattern_denote
    (signature : List Nat) (definition : Fin signature.length)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin (signature.get definition) → model.Carrier) :
    (namedReferencePattern signature definition).denote model named
        (args ∘ Fin.cast
          (namedReferencePattern_boundary_length signature definition)) ↔
      named (signature.get definition)
        (namedReferenceRelation signature definition) args := by
  obtain ⟨body, hcompile, helaborate⟩ :=
    (namedReferencePattern signature definition).elaborate_body_computation
  unfold ConcreteElaboration.compileRoot? at hcompile
  dsimp only [namedReferencePattern] at hcompile
  rw [namedReferencePattern_hidden,
    namedReferencePattern_occurrences] at hcompile
  simp only [ConcreteElaboration.compileOccurrencesWith?,
    ConcreteElaboration.compileOccurrenceWith?] at hcompile
  simp only [ConcreteElaboration.compileNode?,
    namedReferencePatternRaw] at hcompile
  generalize hrelation :
      ConcreteElaboration.namedRel? signature definition.val
        (signature.get definition) = maybeRelation at hcompile
  cases maybeRelation with
  | none =>
      simp [hrelation] at hcompile
  | some relation =>
      generalize harguments :
          ConcreteElaboration.resolvePorts? _ _ _ _ = maybeArguments at hcompile
      cases maybeArguments with
      | none =>
          simp [hrelation, harguments] at hcompile
      | some arguments =>
          simp at hcompile
          have relation_eq :
              relation = namedReferenceRelation signature definition := by
            apply Theory.namedRel_eq_of_index_eq
            apply Fin.ext
            exact (ConcreteElaboration.namedRel?_sound hrelation).1
          subst relation
          let raw := namedReferencePatternRaw signature definition
          let position (index : Fin (signature.get definition)) :
              Fin raw.boundary.length :=
            Fin.cast
              (namedReferencePattern_boundary_length signature
                definition).symm index
          let boundaryIndex (index : Fin (signature.get definition)) :
              Fin (raw.exposedWires ++ []).length :=
            Fin.cast (by simp) (raw.boundaryClass (position index))
          have boundaryWire (index : Fin (signature.get definition)) :
              raw.boundary.get (position index) = index := by
            simpa [raw, position, namedReferencePatternRaw] using
              get_allFin (signature.get definition) (position index)
          have argument_eq (index : Fin (signature.get definition)) :
              arguments index = boundaryIndex index := by
            have hresolved := sequenceFin_sound harguments index
            obtain ⟨wire, hoccurs, hlookup⟩ :=
              ConcreteElaboration.resolvePort?_sound hresolved
            have hwire : wire = index := by
              apply Fin.ext
              have hvalues : index.val = wire.val := by
                simpa [namedReferencePatternRaw,
                  ConcreteDiagram.EndpointOccurs] using hoccurs
              exact hvalues.symm
            have hargumentGet :
                (raw.exposedWires ++ []).get (arguments index) = index :=
              hlookup.trans hwire
            have hboundaryGet :
                (raw.exposedWires ++ []).get (boundaryIndex index) =
                  index := by
              have hs := raw.boundaryClass_sound (position index)
              rw [boundaryWire] at hs
              simpa [boundaryIndex] using hs
            apply Fin.ext
            have hnodup : (raw.exposedWires ++ []).Nodup := by
              simpa using raw.exposedWires_nodup
            let wireContext := raw.exposedWires ++ []
            have hvalues :
                wireContext[(arguments index).val]? =
                  wireContext[(boundaryIndex index).val]? := by
              calc
                wireContext[(arguments index).val]? =
                    some ((raw.exposedWires ++ []).get
                      (arguments index)) := by
                  simpa only [wireContext] using
                    List.getElem?_eq_getElem (arguments index).isLt
                _ = some ((raw.exposedWires ++ []).get
                      (boundaryIndex index)) :=
                  congrArg some (hargumentGet.trans hboundaryGet.symm)
                _ = wireContext[(boundaryIndex index).val]? := by
                  simpa only [wireContext] using
                    (List.getElem?_eq_getElem
                      (boundaryIndex index).isLt).symm
            exact (List.getElem?_inj (arguments index).isLt hnodup).mp
              hvalues
          have hbody :
              (namedReferencePattern signature definition).elaborate.body =
                ConcreteElaboration.finishRoot raw.exposedWires []
                  (.cons
                    (.named
                      (namedReferenceRelation signature definition)
                      arguments)
                    .nil) :=
            helaborate.trans hcompile.symm
          change denoteOpen model named
              (namedReferencePattern signature definition).elaborate
              (args ∘ Fin.cast
                (namedReferencePattern_boundary_length signature
                  definition)) ↔ _
          rw [denoteOpen_iff_assignment, hbody]
          constructor
          · rintro ⟨assignment, assignmentArgs, hdenotes⟩
            unfold ConcreteElaboration.finishRoot at hdenotes
            simp [ItemSeq.castWiresEq_eq_renameWires, denoteRegion,
              denoteItemSeq, ItemSeq.renameWires] at hdenotes
            obtain ⟨_, hitem⟩ := hdenotes
            simp [Item.renameWires, denoteItem] at hitem
            let compiledArgs : Fin (signature.get definition) →
                model.Carrier :=
              fun index => assignment.classes
                (Fin.cast (by
                  change (raw.exposedWires ++ []).length =
                    raw.exposedWires.length
                  simp)
                  (arguments index))
            change named (signature.get definition)
              (namedReferenceRelation signature definition)
              compiledArgs at hitem
            have compiledArgs_eq : compiledArgs = args := by
              funext index
              simp only [compiledArgs, argument_eq]
              calc
                assignment.classes
                    (Fin.cast _ (boundaryIndex index)) =
                    assignment.classes
                      (raw.boundaryClass (position index)) := by
                  congr 1
                _ = assignment.args (position index) :=
                  assignment.agrees (position index)
                _ = (args ∘ Fin.cast
                      (namedReferencePattern_boundary_length signature
                        definition))
                    (position index) :=
                  congrFun assignmentArgs (position index)
                _ = args index := by
                  simp [position, Function.comp_apply]
            exact compiledArgs_eq ▸ hitem
          · intro hnamed
            have aliasConsistent :
                AliasConsistent
                  (namedReferencePattern signature definition).elaborate
                  (args ∘ Fin.cast
                    (namedReferencePattern_boundary_length signature
                      definition)) := by
              intro left right hclasses
              have hraw :
                  raw.boundaryClass left = raw.boundaryClass right :=
                hclasses
              have hwires :=
                (raw.boundaryClass_eq_iff left right).mp hraw
              have leftGet :
                  raw.boundary.get left =
                    Fin.cast
                      (namedReferencePattern_boundary_length signature
                        definition) left := by
                simpa [raw, namedReferencePatternRaw] using
                  get_allFin (signature.get definition) left
              have rightGet :
                  raw.boundary.get right =
                    Fin.cast
                      (namedReferencePattern_boundary_length signature
                        definition) right := by
                simpa [raw, namedReferencePatternRaw] using
                  get_allFin (signature.get definition) right
              have hcast :
                  Fin.cast
                      (namedReferencePattern_boundary_length signature
                        definition) left =
                    Fin.cast
                      (namedReferencePattern_boundary_length signature
                        definition) right :=
                leftGet.symm.trans (hwires.trans rightGet)
              have hpositions : left = right := by
                apply Fin.ext
                simpa using congrArg Fin.val hcast
              subst right
              rfl
            obtain ⟨assignment, assignmentArgs⟩ :=
              (boundaryAssignment_iff_aliasConsistent
                (namedReferencePattern signature definition).elaborate
                (args ∘ Fin.cast
                  (namedReferencePattern_boundary_length signature
                    definition))).2 aliasConsistent
            refine ⟨assignment, assignmentArgs, ?_⟩
            let compiledArgs : Fin (signature.get definition) →
                model.Carrier :=
              fun index => assignment.classes
                (Fin.cast (by
                  change (raw.exposedWires ++ []).length =
                    raw.exposedWires.length
                  simp)
                  (arguments index))
            have compiledArgs_eq : compiledArgs = args := by
              funext index
              simp only [compiledArgs, argument_eq]
              calc
                assignment.classes
                    (Fin.cast _ (boundaryIndex index)) =
                    assignment.classes
                      (raw.boundaryClass (position index)) := by
                  congr 1
                _ = assignment.args (position index) :=
                  assignment.agrees (position index)
                _ = (args ∘ Fin.cast
                      (namedReferencePattern_boundary_length signature
                        definition))
                    (position index) :=
                  congrFun assignmentArgs (position index)
                _ = args index := by
                  simp [position, Function.comp_apply]
            unfold ConcreteElaboration.finishRoot
            simp [ItemSeq.castWiresEq_eq_renameWires, denoteRegion,
              denoteItemSeq, denoteItem, ItemSeq.renameWires,
              Item.renameWires]
            refine ⟨Fin.elim0, ?_⟩
            change named (signature.get definition)
              (namedReferenceRelation signature definition) compiledArgs
            exact compiledArgs_eq.symm ▸ hnamed

private def castNamedRel (relation : NamedRel signature sourceArity)
    (arity_eq : sourceArity = targetArity) :
    NamedRel signature targetArity :=
  arity_eq ▸ relation

private theorem namedEnv_castArity
    (named : NamedEnv D signature)
    (relation : NamedRel signature sourceArity)
    (arity_eq : sourceArity = targetArity)
    (args : Fin sourceArity → D) :
    named sourceArity relation args ↔
      named targetArity (castNamedRel relation arity_eq)
        (args ∘ Fin.cast arity_eq.symm) := by
  subst targetArity
  rfl

private theorem castNamedRel_index
    (relation : NamedRel signature sourceArity)
    (arity_eq : sourceArity = targetArity) :
    (castNamedRel relation arity_eq).index = relation.index := by
  subst targetArity
  rfl

/-- Entry-indexed form of `namedReferencePattern_denote`, with the signature
arity transport normalized to the checked definition body. -/
theorem namedReferencePattern_denote_entry
    (entry : DefinitionEntry signature definition)
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin entry.body.val.boundary.length → model.Carrier) :
    (namedReferencePattern signature definition).denote model named
        ((args ∘ Fin.cast entry.body_arity.symm) ∘
          Fin.cast
            (namedReferencePattern_boundary_length signature definition)) ↔
      named entry.body.val.boundary.length entry.namedRelation args := by
  rw [namedReferencePattern_denote]
  have relation_eq :
      castNamedRel entry.namedRelation entry.body_arity =
        namedReferenceRelation signature definition := by
    apply Theory.namedRel_eq_of_index_eq
    rw [castNamedRel_index]
    rfl
  have transported :=
    namedEnv_castArity named entry.namedRelation entry.body_arity args
  rw [relation_eq] at transported
  exact transported.symm

theorem relFold_namedReference_arity
    (context : ProofContext signature)
    (definition : Fin signature.length)
    (payload : RelFoldPayload input selection definition.val args)
    (body_eq :
      payload.body.val = (context.definitionEntry definition).body.val) :
    payload.body.val.boundary.length =
      (namedReferencePattern signature definition).val.boundary.length := by
  rw [body_eq]
  simpa [namedReferencePattern, namedReferencePatternRaw,
    allFin_eq_finRange] using
    (context.definitionEntry definition).body_arity

theorem relUnfold_body_arity
    (context : ProofContext signature)
    (definition : Fin signature.length)
    (payload : RelUnfoldPayload input node definition)
    (body_eq :
      payload.body.val = (context.definitionEntry definition).body.val) :
    payload.source.val.boundary.length =
      payload.body.val.boundary.length := by
  rw [body_eq]
  exact (wiredNamedReferencePattern_boundary_length signature definition
      payload.wiring).trans
    (context.definitionEntry definition).body_arity.symm

end VisualProof.Rule
