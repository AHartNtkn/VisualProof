import VisualProof.Diagram.FocusIsomorphism

namespace VisualProof.Diagram

open VisualProof.Theory

def DiagramContext.path : DiagramContext outer holeWires → RegionPath
  | .hole => []
  | .cut _ before _ child => before.length :: child.path

/-- Evidence that an identity occurrence is owned directly by the current
region rather than by a nested cut. -/
inductive ItemSeq.IdentityOccurrence.Direct :
    {items : ItemSeq wires} → ItemSeq.IdentityOccurrence items → Prop
  | head {signature : Sig} {arity : Nat}
      {ports : Fin arity → Var wires signature} {tail : ItemSeq wires} :
      Direct (@ItemSeq.IdentityOccurrence.head wires signature arity ports tail)
  | tail {item : Item wires} {tail : ItemSeq wires}
      {node : ItemSeq.IdentityOccurrence tail}
      (direct : @Direct wires tail node) :
      Direct (.tail (item := item) node)

/-- The exact owner region of one recursive identity occurrence, together
with its enclosing context and a presentation isomorphism. -/
structure Region.IdentityOccurrence.Owner
    {region : Region outer} (node : Region.IdentityOccurrence region) where
  ownerOuter : List Sig
  ownerLocals : List Sig
  ownerItems : ItemSeq (ownerOuter ++ ownerLocals)
  ownerNode : ItemSeq.IdentityOccurrence ownerItems
  direct : ownerNode.Direct
  context : DiagramContext outer ownerOuter
  source_eq : context.fill (.mk ownerLocals ownerItems) = region
  path_eq : context.path = node.path

/-- The current-region view computed while resolving an owner. -/
inductive ItemSeq.IdentityOccurrence.Resolved :
    {items : ItemSeq wires} →
    (node : ItemSeq.IdentityOccurrence items) → Type
  | direct (owned : node.Direct) : Resolved node
  | nested {items : ItemSeq wires} {node : ItemSeq.IdentityOccurrence items}
      {body : Region wires}
      (before after : ItemSeq wires)
      (child : Region.IdentityOccurrence body)
      (rebuild : before.append (.cons (.cut body) after) = items)
      (path_eq : ∀ itemIndex,
        node.pathFrom itemIndex = (itemIndex + before.length) :: child.path)
      (owner : child.Owner) : Resolved node

private theorem ItemSeq.IdentityOccurrence.pathFrom_eq_nil_of_direct
    {items : ItemSeq wires} {node : ItemSeq.IdentityOccurrence items}
    (direct : @ItemSeq.IdentityOccurrence.Direct wires items node)
    (itemIndex : Nat) : node.pathFrom itemIndex = [] := by
  induction direct generalizing itemIndex with
  | head => rfl
  | tail _ induction => exact induction (itemIndex + 1)

private noncomputable def ownerItem
    {outer locals : List Sig} {items : ItemSeq (outer ++ locals)}
    (node : ItemSeq.IdentityOccurrence items)
    (resolved : node.Resolved) :
    Region.IdentityOccurrence.Owner (.item node) := by
  cases resolved with
  | direct owned =>
      exact {
        ownerOuter := outer
        ownerLocals := locals
        ownerItems := items
        ownerNode := node
        direct := owned
        context := .hole
        source_eq := rfl
        path_eq := by
          exact (ItemSeq.IdentityOccurrence.pathFrom_eq_nil_of_direct
            owned 0).symm
      }
  | nested before after child rebuild path_eq childOwner =>
      let context : DiagramContext outer childOwner.ownerOuter :=
        .cut locals before after childOwner.context
      exact {
        ownerOuter := childOwner.ownerOuter
        ownerLocals := childOwner.ownerLocals
        ownerItems := childOwner.ownerItems
        ownerNode := childOwner.ownerNode
        direct := childOwner.direct
        context := context
        source_eq := by
          simp only [context, DiagramContext.fill]
          rw [childOwner.source_eq, rebuild]
        path_eq := by
          simp only [Region.IdentityOccurrence.path]
          change before.length :: childOwner.context.path = node.pathFrom 0
          rw [childOwner.path_eq, path_eq 0]
          simp
      }

private def resolvedHead :
    (@ItemSeq.IdentityOccurrence.head wires signature arity ports tail).Resolved :=
  .direct .head

private noncomputable def resolvedHeadCut
    (node : Region.IdentityOccurrence body) (owner : node.Owner) :
    (ItemSeq.IdentityOccurrence.headCut (tail := tail) node).Resolved :=
  .nested .nil tail node rfl (by intro itemIndex; rfl) owner

private noncomputable def resolvedTail
    {item : Item wires} {tail : ItemSeq wires}
    (node : ItemSeq.IdentityOccurrence tail) (resolved : node.Resolved) :
    (@ItemSeq.IdentityOccurrence.tail wires tail item node).Resolved := by
  cases resolved with
  | direct owned => exact .direct (.tail owned)
  | nested before after child rebuild path_eq owner =>
      exact .nested (.cons item before) after child (by
        simp only [ItemSeq.append]
        rw [rebuild]) (by
          intro itemIndex
          rw [ItemSeq.IdentityOccurrence.pathFrom, path_eq (itemIndex + 1)]
          simp [ItemSeq.length]
          omega) owner

noncomputable def Region.IdentityOccurrence.owner
    {region : Region outer} (node : Region.IdentityOccurrence region) :
    node.Owner :=
  Region.IdentityOccurrence.rec
    (motive_1 := fun _ node => node.Owner)
    (motive_2 := fun _ node => node.Resolved)
    ownerItem resolvedHead resolvedHeadCut resolvedTail node

end VisualProof.Diagram
