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

private theorem wiredNamedReferencePattern_hidden
    (signature : List Nat) (definition : Fin signature.length)
    (wiring : NamedReferenceWiring (signature.get definition)) :
    (wiredNamedReferencePatternRaw signature definition wiring).hiddenWires =
      [] := by
  rw [OpenConcreteDiagram.hiddenWires]
  simp only [wiredNamedReferencePatternRaw,
    ConcreteElaboration.exactScopeWires, List.filter_eq_nil_iff]
  intro wire _
  simp only [Bool.not_eq_true, decide_eq_false_iff_not]
  intro hnot
  obtain ⟨argument, hargument⟩ := wiring.argumentWire_surjective wire
  apply hnot
  unfold OpenConcreteDiagram.exposedWires
  change wire ∈ (List.ofFn wiring.argumentWire).eraseDups
  rw [List.mem_eraseDups]
  rw [← hargument]
  exact List.mem_ofFn.mpr ⟨argument, rfl⟩

private theorem wiredNamedReferencePattern_occurrences
    (signature : List Nat) (definition : Fin signature.length)
    (wiring : NamedReferenceWiring (signature.get definition)) :
    ConcreteElaboration.localOccurrences
        (wiredNamedReferencePatternRaw signature definition wiring).diagram
        (wiredNamedReferencePatternRaw signature definition wiring).diagram.root =
      [.node ⟨0, by simp [wiredNamedReferencePatternRaw]⟩] := by
  simp [wiredNamedReferencePatternRaw,
    ConcreteElaboration.localOccurrences, filterFin, allFin_eq_finRange,
    List.finRange_succ_last, CNode.region, CRegion.parent?]
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

/-- Boundary arguments respect the concrete identity quotient selected by a
wired named-reference occurrence. -/
def NamedReferenceWiring.Consistent
    (wiring : NamedReferenceWiring arity) (args : Fin arity → D) : Prop :=
  ∀ left right, wiring.argumentWire left = wiring.argumentWire right →
    args left = args right

/-- A one-node named reference with an arbitrary concrete wire quotient denotes
its named relation exactly when the supplied boundary values respect that
quotient. -/
theorem wiredNamedReferencePattern_denote
    (signature : List Nat) (definition : Fin signature.length)
    (wiring : NamedReferenceWiring (signature.get definition))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin (signature.get definition) → model.Carrier) :
    (wiredNamedReferencePattern signature definition wiring).denote model named
        (args ∘ Fin.cast
          (wiredNamedReferencePattern_boundary_length signature definition
            wiring)) ↔
      wiring.Consistent args ∧
        named (signature.get definition)
          (namedReferenceRelation signature definition) args := by
  obtain ⟨body, hcompile, helaborate⟩ :=
    (wiredNamedReferencePattern signature definition wiring).elaborate_body_computation
  unfold ConcreteElaboration.compileRoot? at hcompile
  dsimp only [wiredNamedReferencePattern] at hcompile
  rw [wiredNamedReferencePattern_hidden signature definition wiring,
    wiredNamedReferencePattern_occurrences signature definition wiring] at hcompile
  simp only [ConcreteElaboration.compileOccurrencesWith?,
    ConcreteElaboration.compileOccurrenceWith?] at hcompile
  simp only [ConcreteElaboration.compileNode?,
    wiredNamedReferencePatternRaw] at hcompile
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
          let raw :=
            wiredNamedReferencePatternRaw signature definition wiring
          let position (index : Fin (signature.get definition)) :
              Fin raw.boundary.length :=
            Fin.cast
              (wiredNamedReferencePattern_boundary_length signature definition
                wiring).symm index
          have cast_position (index : Fin (signature.get definition)) :
              Fin.cast
                  (wiredNamedReferencePattern_boundary_length signature
                    definition wiring)
                  (position index) = index := by
            apply Fin.ext
            rfl
          let boundaryIndex (index : Fin (signature.get definition)) :
              Fin (raw.exposedWires ++ []).length :=
            Fin.cast (by simp) (raw.boundaryClass (position index))
          have boundaryWire (index : Fin (signature.get definition)) :
              raw.boundary.get (position index) = wiring.argumentWire index := by
            simpa [raw, position, wiredNamedReferencePatternRaw,
              List.get_eq_getElem] using
              List.get_ofFn wiring.argumentWire (position index)
          have argument_eq (index : Fin (signature.get definition)) :
              arguments index = boundaryIndex index := by
            have hresolved := sequenceFin_sound harguments index
            obtain ⟨wire, hoccurs, hlookup⟩ :=
              ConcreteElaboration.resolvePort?_sound hresolved
            have hwire : wire = wiring.argumentWire index := by
              have hmember :
                  ({ node := 0, port := CPort.arg index } : CEndpoint 1) ∈
                    (allFin (signature.get definition)).filterMap
                      (fun argument =>
                        if wiring.argumentWire argument = wire then
                          some { node := 0, port := CPort.arg argument }
                        else none) := by
                simpa [raw, wiredNamedReferencePatternRaw,
                  ConcreteDiagram.EndpointOccurs] using hoccurs
              obtain ⟨argument, _, hmapped⟩ := List.mem_filterMap.mp hmember
              by_cases heq : wiring.argumentWire argument = wire
              · rw [if_pos heq] at hmapped
                have hindex : argument = index := by
                  have := Option.some.inj hmapped
                  apply Fin.ext
                  simpa using congrArg
                    (fun endpoint : CEndpoint 1 => endpoint.port) this
                subst argument
                exact heq.symm
              · simp [heq] at hmapped
            have hargumentGet :
                (raw.exposedWires ++ []).get (arguments index) =
                  wiring.argumentWire index :=
              hlookup.trans hwire
            have hboundaryGet :
                (raw.exposedWires ++ []).get (boundaryIndex index) =
                  wiring.argumentWire index := by
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
              (wiredNamedReferencePattern signature definition wiring).elaborate.body =
                ConcreteElaboration.finishRoot raw.exposedWires []
                  (.cons
                    (.named
                      (namedReferenceRelation signature definition)
                      arguments)
                    .nil) :=
            helaborate.trans hcompile.symm
          change denoteOpen model named
              (wiredNamedReferencePattern signature definition wiring).elaborate
              (args ∘ Fin.cast
                (wiredNamedReferencePattern_boundary_length signature
                  definition wiring)) ↔ _
          rw [denoteOpen_iff_assignment, hbody]
          constructor
          · rintro ⟨assignment, assignmentArgs, hdenotes⟩
            have consistent : wiring.Consistent args := by
              intro left right hwires
              let leftPosition := position left
              let rightPosition := position right
              have hclasses :
                  raw.boundaryClass leftPosition =
                    raw.boundaryClass rightPosition := by
                apply (raw.boundaryClass_eq_iff leftPosition rightPosition).2
                change raw.boundary.get (position left) =
                  raw.boundary.get (position right)
                rw [boundaryWire, boundaryWire]
                exact hwires
              have assignmentAt (index : Fin (signature.get definition)) :
                  assignment.args (position index) = args index := by
                rw [assignmentArgs]
                change args (Fin.cast _ (position index)) = args index
                rw [cast_position]
              calc
                args left = assignment.args leftPosition := by
                  exact (assignmentAt left).symm
                _ = assignment.classes (raw.boundaryClass leftPosition) :=
                  (assignment.agrees leftPosition).symm
                _ = assignment.classes (raw.boundaryClass rightPosition) := by
                  rw [hclasses]
                _ = assignment.args rightPosition :=
                  assignment.agrees rightPosition
                _ = args right := assignmentAt right
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
                      (wiredNamedReferencePattern_boundary_length signature
                        definition wiring))
                    (position index) :=
                  congrFun assignmentArgs (position index)
                _ = args index := by
                  simp [position, Function.comp_apply]
            exact ⟨consistent, compiledArgs_eq ▸ hitem⟩
          · rintro ⟨consistent, hnamed⟩
            have aliasConsistent :
                AliasConsistent
                  (wiredNamedReferencePattern signature definition wiring).elaborate
                  (args ∘ Fin.cast
                    (wiredNamedReferencePattern_boundary_length signature
                      definition wiring)) := by
              intro left right hclasses
              have hraw : raw.boundaryClass left = raw.boundaryClass right :=
                hclasses
              have hwires := (raw.boundaryClass_eq_iff left right).mp hraw
              have leftGet :
                  raw.boundary.get left =
                    wiring.argumentWire
                      (Fin.cast
                        (wiredNamedReferencePattern_boundary_length signature
                          definition wiring) left) := by
                simp [raw, wiredNamedReferencePatternRaw,
                  List.get_eq_getElem]
                apply congrArg wiring.argumentWire
                apply Fin.ext
                rfl
              have rightGet :
                  raw.boundary.get right =
                    wiring.argumentWire
                      (Fin.cast
                        (wiredNamedReferencePattern_boundary_length signature
                          definition wiring) right) := by
                simp [raw, wiredNamedReferencePatternRaw,
                  List.get_eq_getElem]
                apply congrArg wiring.argumentWire
                apply Fin.ext
                rfl
              apply consistent
              exact leftGet.symm.trans (hwires.trans rightGet)
            obtain ⟨assignment, assignmentArgs⟩ :=
              (boundaryAssignment_iff_aliasConsistent
                (wiredNamedReferencePattern signature definition wiring).elaborate
                (args ∘ Fin.cast
                  (wiredNamedReferencePattern_boundary_length signature
                    definition wiring))).2 aliasConsistent
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
                      (wiredNamedReferencePattern_boundary_length signature
                        definition wiring))
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

/-- Entry-indexed form of `wiredNamedReferencePattern_denote`. The named
relation is normalized to the checked body arity while the consistency premise
remains on the occurrence's ordered argument interface. -/
theorem wiredNamedReferencePattern_denote_entry
    (entry : DefinitionEntry signature definition)
    (wiring : NamedReferenceWiring (signature.get definition))
    (model : Lambda.LambdaModel)
    (named : NamedEnv model.Carrier signature)
    (args : Fin entry.body.val.boundary.length → model.Carrier) :
    (wiredNamedReferencePattern signature definition wiring).denote model named
        ((args ∘ Fin.cast entry.body_arity.symm) ∘
          Fin.cast
            (wiredNamedReferencePattern_boundary_length signature definition
              wiring)) ↔
      wiring.Consistent (args ∘ Fin.cast entry.body_arity.symm) ∧
        named entry.body.val.boundary.length entry.namedRelation args := by
  rw [wiredNamedReferencePattern_denote]
  have relation_eq :
      castNamedRel entry.namedRelation entry.body_arity =
        namedReferenceRelation signature definition := by
    apply Theory.namedRel_eq_of_index_eq
    rw [castNamedRel_index]
    rfl
  have transported :=
    namedEnv_castArity named entry.namedRelation entry.body_arity args
  rw [relation_eq] at transported
  constructor
  · rintro ⟨consistent, hnamed⟩
    exact ⟨consistent, transported.mpr hnamed⟩
  · rintro ⟨consistent, hnamed⟩
    exact ⟨consistent, transported.mp hnamed⟩

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
