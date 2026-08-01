import VisualProof.Diagram.Concrete.WirePrimitive.ArgumentsCylindrificationRecursiveConstruction

namespace VisualProof
namespace ConcreteWirePrimitive
namespace ArgumentsSemantics

open WirePrimitive

private theorem recursive_argumentOrigins_get
    (diagram : ConcreteDiagram definitionCount)
    (context : ConcreteElaboration.WireContext diagram)
    (node : diagram.NodeId)
    (start : Nat)
    {argumentSigs : List Sig}
    (values : Vars context.sigs argumentSigs)
    (origins :
      ConcreteElaboration.ArgumentOrigins diagram context node start values)
    (index : Nat)
    (bound : index < argumentSigs.length) :
    diagram.endpointOwner? ⟨node, .arg (start + index)⟩ =
      some ((ConcreteElaboration.variableOrigins diagram context values).get
        ⟨index, by
          simpa [TypedArguments.variableOrigins_length] using bound⟩) := by
  induction values generalizing start index with
  | nil => simp at bound
  | @cons signature rest head tail induction =>
      cases index with
      | zero =>
          simpa [ConcreteElaboration.ArgumentOrigins,
            ConcreteElaboration.variableOrigins] using origins.1
      | succ index =>
          have tailBound : index < rest.length := by simpa using bound
          have tailExact := induction (start := start + 1) origins.2
            index tailBound
          simpa [ConcreteElaboration.variableOrigins, Nat.add_assoc,
            Nat.add_comm, Nat.add_left_comm] using tailExact

/-- Any checked application local to a recursively compiled region has the
same atom head and ordered concrete argument owners in that region's exact
compiler context.  Unlike the root-only frame lemma, this statement uses
the authoritative `compileNodes?` equation supplied by region recursion. -/
theorem compileAppliedSiteAt?_complete
    {source : CheckedDiagram definitions}
    {wire : source.val.WireId}
    (context : ConcreteElaboration.WireContext source.val)
    (region : source.val.RegionId)
    (items : ItemSeq definitions context.sigs)
    (compiled :
      ConcreteElaboration.compileNodes? definitions source.val context
          (source.val.nodesAt region) = some items)
    (site : AppliedSite source wire)
    (siteRegion : site.region = region) :
    ∃ (head : Var context.sigs (.rel site.argumentSignatures))
      (arguments : Vars context.sigs site.argumentSignatures),
      ConcreteElaboration.Internal.compileNode? definitions source.val
          context site.node = some (.atom head arguments) ∧
      ConcreteElaboration.WireContext.origin source.val context.ids head =
        wire ∧
      ConcreteElaboration.variableOrigins source.val context arguments =
        site.arguments := by
  have nodeMember : site.node ∈ source.val.nodesAt region := by
    unfold ConcreteDiagram.nodesAt ConcreteDiagram.nodesList
    apply List.mem_filter.mpr
    refine ⟨Data.Finite.mem_allFin site.node, ?_⟩
    rw [site.node_data, siteRegion]
    exact beq_iff_eq.mpr rfl
  obtain ⟨item, singletonCompiled⟩ :=
    ConcreteWireQuantifier.SingletonRemovalSemantics.compileNodes_singleton_of_member
      definitions source.val context (source.val.nodesAt region) items
      compiled site.node nodeMember
  obtain ⟨head, arguments, itemExact, headOrigin, argumentOrigins⟩ :=
    ConcreteElaboration.compileNodes?_atom_shape source.val context site.node
      site.node_data singletonCompiled
  have itemSame : item = .atom head arguments :=
    ItemSeq.cons.inj itemExact |>.1
  subst item
  have nodeCompiled :
      ConcreteElaboration.Internal.compileNode? definitions source.val
          context site.node = some (.atom head arguments) := by
    cases found : ConcreteElaboration.Internal.compileNode? definitions
        source.val context site.node with
    | none =>
        simp [ConcreteElaboration.compileNodes?, found] at singletonCompiled
    | some foundItem =>
        have foundExact : foundItem = .atom head arguments := by
          simpa [ConcreteElaboration.compileNodes?, found] using
            singletonCompiled
        simpa [foundExact] using found
  have headExact :
      ConcreteElaboration.WireContext.origin source.val context.ids head =
        wire :=
    Option.some.inj (headOrigin.symm.trans site.endpoint_owner)
  have argumentsExact :
      ConcreteElaboration.variableOrigins source.val context arguments =
        site.arguments := by
    apply List.ext_get
    · simpa [TypedArguments.variableOrigins_length] using
        site.arguments_length.symm
    · intro index leftBound rightBound
      have compiledOwner := recursive_argumentOrigins_get source.val context
        site.node 0 arguments argumentOrigins index (by
          rw [← TypedArguments.variableOrigins_length source.val context
            arguments]
          exact leftBound)
      have siteOwner := site.argument_owner index rightBound
      exact Option.some.inj (compiledOwner.symm.trans (by
        simpa using siteOwner))
  exact ⟨head, arguments, nodeCompiled, headExact, argumentsExact⟩

/-- Assemble a cylindrical-hole receipt from exact ordered lengths, the two
finite order equivalences, and one pointwise split equation.  Root and
descendant arity blocks differ only in how they prove that equation. -/
noncomputable def cylindricalHolesOfSplit
    (insertion :
      TypedArguments.InsertionEvidence largerArguments smallerArguments
        fixedSignature)
    (bounds :
      BoundCylindrification fixedSignature smallerBound largerBound
        freshCount)
    (outer : WireRenaming smallerOuter largerOuter)
    (smaller :
      List (Vars (smallerBound ++ smallerOuter) smallerArguments))
    (larger :
      List (Vars (largerBound ++ largerOuter) largerArguments))
    (smallerLength : smaller.length = freshCount)
    (largerLength : larger.length = freshCount)
    (sourceOrder : Data.Finite.FiniteEquiv (Fin freshCount) (Fin freshCount))
    (freshOrder : Data.Finite.FiniteEquiv (Fin freshCount) (Fin freshCount))
    (splitExact : ∀ index : Fin freshCount,
      insertion.splitVars
          (larger.get (Fin.cast largerLength.symm index)) =
        ⟨bounds.freshVar outer (freshOrder index),
          Vars.rename (bounds.embed outer)
            (smaller.get
              (Fin.cast smallerLength.symm (sourceOrder index)))⟩) :
    CylindricalHoles insertion bounds outer smaller larger :=
  { smaller_length := smallerLength
    larger_length := largerLength
    sourceIndex := sourceOrder
    sourceIndex_injective := sourceOrder.injective
    sourceIndex_surjective := fun target =>
      ⟨sourceOrder.invFun target, sourceOrder.right_inv target⟩
    freshIndex := freshOrder
    freshIndex_injective := freshOrder.injective
    freshIndex_surjective := fun target =>
      ⟨freshOrder.invFun target, freshOrder.right_inv target⟩
    inserted_exact := fun index => congrArg Prod.fst (splitExact index)
    retained_exact := fun index => congrArg Prod.snd (splitExact index) }

end ArgumentsSemantics
end ConcreteWirePrimitive
end VisualProof
