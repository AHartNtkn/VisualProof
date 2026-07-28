import VisualProof.Diagram.Semantics

namespace VisualProof

universe u

namespace Region

/-- Surround one region's conjunction by fixed items at the same typed scope. -/
def surround (leading : ItemSeq defs ctx) (body : Region defs ctx)
    (suffix : ItemSeq defs ctx) : Region defs ctx :=
  match body with
  | .mk items => .mk (leading.append (items.append suffix))

@[simp] theorem denote_surround
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (env : Env pre ctx) (leading suffix : ItemSeq defs ctx)
    (body : Region defs ctx) :
    denoteRegion pre definitionEnv env (surround leading body suffix) ↔
      denoteItemSeq pre definitionEnv env leading ∧
      denoteRegion pre definitionEnv env body ∧
      denoteItemSeq pre definitionEnv env suffix := by
  cases body
  simp only [surround, denoteRegion, denoteItemSeq_append]

end Region

/--
A genuine typed one-hole diagram context. `holeCtx` is the wire context expected
by the hole and `outerCtx` is the context exposed after all recorded binders.
Conjunction frames, cuts, and binders each own exactly one recursive child.
-/
inductive DiagramContext (defs : List (List Sig)) :
    List Sig → List Sig → Type
  | hole : DiagramContext defs ctx ctx
  | surround (leading : ItemSeq defs outerCtx)
      (inner : DiagramContext defs holeCtx outerCtx)
      (suffix : ItemSeq defs outerCtx) :
      DiagramContext defs holeCtx outerCtx
  | cut (inner : DiagramContext defs holeCtx outerCtx) :
      DiagramContext defs holeCtx outerCtx
  | bind (sig : Sig)
      (inner : DiagramContext defs holeCtx (sig :: outerCtx)) :
      DiagramContext defs holeCtx outerCtx

namespace DiagramContext

/-- Fill the unique hole; typing prevents wire capture at every binder. -/
def fill : DiagramContext defs holeCtx outerCtx →
    Region defs holeCtx → Region defs outerCtx
  | .hole, body => body
  | .surround leading inner suffix, body =>
      Region.surround leading (inner.fill body) suffix
  | .cut inner, body =>
      .mk (.cons (.cut (inner.fill body)) .nil)
  | .bind sig inner, body =>
      .mk (.cons (.bind sig (inner.fill body)) .nil)

/-- Number of negating cuts between the outer region and the hole. -/
def cutDepth : DiagramContext defs holeCtx outerCtx → Nat
  | .hole => 0
  | .surround _ inner _ => inner.cutDepth
  | .cut inner => inner.cutDepth + 1
  | .bind _ inner => inner.cutDepth

/-- Ordered signatures of binders crossed from the outside toward the hole. -/
def binderPath : DiagramContext defs holeCtx outerCtx → List Sig
  | .hole => []
  | .surround _ inner _ => inner.binderPath
  | .cut inner => inner.binderPath
  | .bind sig inner => sig :: inner.binderPath

private def SemanticDirection (depth : Nat) (left right : Prop) : Prop :=
  if depth % 2 = 0 then left → right else right → left

private theorem mod_two_cases (value : Nat) :
    value % 2 = 0 ∨ value % 2 = 1 := by
  have bound := Nat.mod_lt value (by decide : 0 < 2)
  omega

/--
The semantic direction of a one-hole context is determined solely by cut
parity. The proof follows the actual context constructors; no entailment is
stored in the context.
-/
private theorem transport
    (context : DiagramContext defs holeCtx outerCtx)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (left right : Region defs holeCtx)
    (entails : ∀ env : Env pre holeCtx,
      denoteRegion pre definitionEnv env left →
        denoteRegion pre definitionEnv env right) :
    ∀ env : Env pre outerCtx,
      SemanticDirection context.cutDepth
        (denoteRegion pre definitionEnv env (context.fill left))
        (denoteRegion pre definitionEnv env (context.fill right)) := by
  induction context with
  | hole =>
      intro env
      simpa [SemanticDirection, cutDepth, fill] using entails env
  | surround leading inner suffix induction =>
      intro env
      have middle := induction left right entails env
      rcases mod_two_cases inner.cutDepth with even | odd
      · simp only [SemanticDirection, cutDepth, even, if_pos] at middle ⊢
        intro source
        simp only [fill] at source ⊢
        rw [Region.denote_surround] at source ⊢
        exact ⟨source.1, middle source.2.1, source.2.2⟩
      · have notEven : inner.cutDepth % 2 ≠ 0 := by omega
        simp only [SemanticDirection, cutDepth, notEven] at middle ⊢
        intro source
        simp only [fill] at source ⊢
        rw [Region.denote_surround] at source ⊢
        exact ⟨source.1, middle source.2.1, source.2.2⟩
  | cut inner induction =>
      intro env
      have middle := induction left right entails env
      rcases mod_two_cases inner.cutDepth with even | odd
      · have successorOdd : (inner.cutDepth + 1) % 2 = 1 := by omega
        have successorNotEven : (inner.cutDepth + 1) % 2 ≠ 0 := by omega
        simp only [SemanticDirection, even, if_pos] at middle
        simp only [SemanticDirection, cutDepth, successorNotEven,
          fill, denoteRegion, denoteItemSeq, denoteItem]
        rintro ⟨rightNot, _⟩
        exact ⟨fun leftDenotes => rightNot (middle leftDenotes), trivial⟩
      · have notEven : inner.cutDepth % 2 ≠ 0 := by omega
        have successorEven : (inner.cutDepth + 1) % 2 = 0 := by omega
        simp only [SemanticDirection, notEven] at middle
        simp only [SemanticDirection, cutDepth, successorEven, if_pos,
          fill, denoteRegion, denoteItemSeq, denoteItem]
        rintro ⟨leftNot, _⟩
        exact ⟨fun rightDenotes => leftNot (middle rightDenotes), trivial⟩
  | bind sig inner induction =>
      intro env
      have middle := fun value => induction left right entails (env.extend value)
      rcases mod_two_cases inner.cutDepth with even | odd
      · simp only [SemanticDirection, cutDepth, even, if_pos] at middle ⊢
        simp only [fill, denoteRegion, denoteItemSeq, denoteItem]
        rintro ⟨⟨value, body⟩, _⟩
        exact ⟨⟨value, middle value body⟩, trivial⟩
      · have notEven : inner.cutDepth % 2 ≠ 0 := by omega
        simp only [SemanticDirection, cutDepth, notEven] at middle ⊢
        simp only [fill, denoteRegion, denoteItemSeq, denoteItem]
        rintro ⟨⟨value, body⟩, _⟩
        exact ⟨⟨value, middle value body⟩, trivial⟩

/-- Even-cut contexts transport entailment in the forward direction. -/
theorem context_mono
    (context : DiagramContext defs holeCtx outerCtx)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (left right : Region defs holeCtx)
    (even : context.cutDepth % 2 = 0)
    (entails : ∀ env : Env pre holeCtx,
      denoteRegion pre definitionEnv env left →
        denoteRegion pre definitionEnv env right)
    (env : Env pre outerCtx) :
    denoteRegion pre definitionEnv env (context.fill left) →
      denoteRegion pre definitionEnv env (context.fill right) := by
  have transported := transport context pre definitionEnv left right entails env
  simpa [SemanticDirection, even] using transported

/-- Odd-cut contexts reverse semantic entailment. -/
theorem context_anti
    (context : DiagramContext defs holeCtx outerCtx)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (left right : Region defs holeCtx)
    (odd : context.cutDepth % 2 = 1)
    (entails : ∀ env : Env pre holeCtx,
      denoteRegion pre definitionEnv env left →
        denoteRegion pre definitionEnv env right)
    (env : Env pre outerCtx) :
    denoteRegion pre definitionEnv env (context.fill right) →
      denoteRegion pre definitionEnv env (context.fill left) := by
  have notEven : context.cutDepth % 2 ≠ 0 := by omega
  have transported := transport context pre definitionEnv left right entails env
  simpa [SemanticDirection, notEven] using transported

/-- Semantic equivalence fills through every context, at every cut depth. -/
theorem context_equiv
    (context : DiagramContext defs holeCtx outerCtx)
    (pre : PreModel.{u}) (definitionEnv : DefinitionEnv pre defs)
    (left right : Region defs holeCtx)
    (equivalent : ∀ env : Env pre holeCtx,
      denoteRegion pre definitionEnv env left ↔
        denoteRegion pre definitionEnv env right)
    (env : Env pre outerCtx) :
    denoteRegion pre definitionEnv env (context.fill left) ↔
      denoteRegion pre definitionEnv env (context.fill right) := by
  rcases mod_two_cases context.cutDepth with even | odd
  · constructor
    · exact context_mono context pre definitionEnv left right even
        (fun holeEnv => (equivalent holeEnv).mp) env
    · exact context_mono context pre definitionEnv right left even
        (fun holeEnv => (equivalent holeEnv).mpr) env
  · constructor
    · exact context_anti context pre definitionEnv right left odd
        (fun holeEnv => (equivalent holeEnv).mpr) env
    · exact context_anti context pre definitionEnv left right odd
        (fun holeEnv => (equivalent holeEnv).mp) env

end DiagramContext

export DiagramContext (context_mono context_anti context_equiv)

namespace ContextExamples

/-- One binder and one cut exercise both context indices and negative polarity. -/
def binderCut : DiagramContext [] [.iota] [] :=
  .bind .iota (.cut .hole)

example : binderCut.binderPath = [.iota] := rfl

example : binderCut.cutDepth = 1 := rfl

private def noDefinitions (pre : PreModel) : DefinitionEnv pre [] :=
  fun {_} definition => nomatch definition

example
    (pre : PreModel) (left right : Region [] [.iota])
    (entails : ∀ env : Env pre [.iota],
      denoteRegion pre (noDefinitions pre) env left →
        denoteRegion pre (noDefinitions pre) env right)
    (env : Env pre []) :
    denoteRegion pre (noDefinitions pre) env
        (binderCut.fill right) →
      denoteRegion pre (noDefinitions pre) env
        (binderCut.fill left) :=
  context_anti binderCut pre (noDefinitions pre)
    left right rfl entails env

end ContextExamples

end VisualProof
