# Proof-Dependent Semantic Simulation

## Outcome

The Lean formalization has one shared compiler-simulation framework capable of
proving every accepted rule receipt, including canonical replacements whose
source and target open boundaries have different alias partitions. The framework
does not demand semantic equalities before the source denotation that entails
them, and it does not assert context mappings outside the concrete contexts
actually traversed by the compiler.

## Semantic dependency order

For either simulation direction, the authoritative proposition is an implication
from the complete active-side denotation to the existence of the opposite-side
semantic witnesses and denotation. Existential choices follow their evidence:

1. obtain the active source root or region denotation;
2. expose its local environment and compiled-item denotation;
3. derive any quotient or coalescence equalities justified by that denotation;
4. construct the target local environment and environment-agreement proof;
5. transport compiled-item truth through the shared recursive simulation; and
6. reconstruct the target region, root, and ordered open denotation.

The backward direction uses the same structure with source and target roles
reversed. Negated cuts flip only the implication direction; bubbles preserve it
and transport the relation witness existentially.

## Authoritative components

`ContextIndexRelation` remains the semantic relation between concrete lexical
indices. `ItemSimulation`, `ItemSeqSimulation`, and `RegionSimulation` remain
useful only where both environments and their agreement are already available.

The witness layer is rebuilt:

- a proof-dependent local transport receives the active compiled-item denotation
  before producing the opposite local environment and extended agreement;
- a proof-dependent root transport has the analogous order for hidden root
  wires;
- a proof-dependent boundary transport receives the active open-body denotation
  before producing the opposite ordered boundary assignment;
- context extension receives exactness evidence for the concrete extended
  source and target contexts, so it does not quantify over unrelated regions.

`finishRegion_denote`, `finishRoot_denote`, and `denoteOpen_lift` consume these
witnesses in that order. `ConcreteSemanticSimulation.compileRegion_denote` and
`compileRoot_denote` remain the sole recursive compiler traversal. Rule modules
supply structural context evidence and their local logical kernel; they do not
implement another traversal.

## Focused replacement and contextual truth

A distinguished replacement may justify equality between wire classes observed
outside its immediate region. Regular ancestor reconstruction therefore passes
the active conjunction proof to local transport before selecting target locals.
This lets a rule-specific witness project the focused conjunct and derive the
needed equality while the shared simulation continues to own traversal,
polarity, binders, and reconstruction.

If a rule's focus is the root, its focused root kernel remains a direct instance
of the same implication-shaped contract. It is not a second framework.

## Migration

Replace `DirectionalLocalWitness`, `DirectionalRootWitness`, and
`DirectionalBoundaryWitness` with proof-dependent definitions rather than adding
parallel variants. Restrict `extendContext` to exact compiler-produced extended
contexts. Migrate base, structural, equational, and high-level consumers, then
delete assumptions and private recursive proofs displaced by the shared API.

The conversion and wire-sever proofs already established against unconditional
structural facts may retain those facts, but their public lifting must use the new
witness order. Wire join must use a concrete context relation that reflects its
scope change rather than a total arbitrary-region map.

## Decisive validation

Validation must include:

- Lean examples in both directions where equal boundary arity has strictly
  different alias partitions and the required equality follows only from the
  active diagram denotation;
- successful wire-join compilation without a false global context lookup law;
- focused builds for every migrated rule family;
- one exhaustive public receipt dispatcher covering all twenty-five rules;
- source scans proving that the displaced witness definitions, rule-local
  recursive simulations, `sorry`, `admit`, and custom axioms are absent; and
- full `lake build`, audit build, Lean/TypeScript tag and matcher correspondence,
  TypeScript typecheck, and runtime test suite.

General proof-system completeness is not asserted. Exact finite occurrence
matching completeness and conditional beta-eta matching completeness remain the
separate scoped completeness results.

## Semantic transport correction

The local and root witness contracts are implication-shaped, not
agreement-shaped. A contextual denotation under cuts can be true because a
sibling is false, so it need not expose any valuation for the distinguished
subdiagram. Requiring an opposite local valuation with full extended-context
agreement before transporting item truth is therefore stronger than logical
validity.

`finishRegion_denote` and `finishRoot_denote` consume a directional transport
that takes the active local valuation and item-sequence denotation together and
returns an opposite local valuation together with the opposite item-sequence
denotation. Regular structural simulations may derive this transport from
environment agreement plus `ItemSeqSimulation`; that decomposition is an
adapter, not the authoritative interface.

Focused replacement transports the whole implication through its retained
compiler context using the existing cut/bubble traversal and contextual
monotonicity. It does not extract focused denotation from a masked negative
branch. Any route or trace evidence is advanced during the shared compiler
recursion from the compile results already in scope; a rule module must not run
a second recursive compiler traversal afterward.
