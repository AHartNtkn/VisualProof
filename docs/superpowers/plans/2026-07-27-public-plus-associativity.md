# Public Plus Associativity Implementation Plan

**Goal:** Prove public `plusAssoc` from exact closed carrier-base and carrier-hereditary support theorems.

**Architecture:** `arithmetic-assoc-base.ts` owns `Base(A)` and `arithmetic-assoc-carrier.ts` owns `Closure(A)`, where `A` is the direct strongest associativity carrier. `arithmetic-assoc.ts` registers both supports before `plusAssoc`; the consumer cites both, grounds the two distinct Nat premises directly to `A`, obtains the inner sum from `A(b)` totality, and obtains the outer sum from `A(a)` transport.

**Tech Stack:** TypeScript, existential graphs, primitive proof actions, canonical diagram replay, Vitest.

## Global Constraints

- Central `ArithmeticStatements` members are the only statement authorities.
- Register theorem order: `associativityCarrierBase`, `associativityCarrierHereditary`, `plusAssoc`.
- Both support citations must be causally indispensable.
- Unfold both distinct public Nat nodes and ground each property wire exactly once to `associativityCarrierContent()` with `[Plus]`.
- `A(b)` totality must causally supply `Plus(b,c,u)`.
- Remove helper induction, reification reference, `refSpawn`, and `induction-statements` paths from the associativity module.

---

### Task 1: Closed carrier base

**Files:**
- Create: `src/theories/arithmetic-assoc-base.ts`

**Interfaces:**
- Consumes: `statements.associativityCarrierBase`
- Produces: `associativityCarrierBase(statements, context): Theorem`

- [x] **Step 1: Derive carrier totality from addition base**

Use right=input as the witness and discharge the exact totality component.

- [x] **Step 2: Derive carrier transport**

Use two addition-base specializations and addition functionality to retarget the inner premise and discharge both exact transport goals.

- [x] **Step 3: Verify the standalone proof model**

The selected proof meets canonically with 44 forward and 33 backward primitive actions.

- [x] **Step 4: Port and verify against central authority**

Use `statements.associativityCarrierBase`; run production replay, `checkTheorem`, and registration.

### Task 2: Public associativity consumer

**Files:**
- Replace: `src/theories/arithmetic-assoc.ts`
- Modify: `src/theories/frege.ts`

**Interfaces:**
- Consumes: `associativityCarrierBase`, `associativityCarrierHereditary`
- Produces: `buildArithmeticAssociativityTheorems(relations, prefix, statements): readonly Theorem[]`

- [x] **Step 1: Verify support composition boundary**

Register both supports, root-cite hereditary support, cite base support inside its positive conclusion, specialize the three primitive relations, discharge the nested standing hypotheses, and expose exact `Base(A)`.

- [x] **Step 2: Build the public midpoint**

Open the exact five-binder public claim, copy `Base(A)` and `Closure(A)` for both Nat obligations, retain the two public Plus premises, and construct the derived inner and outer Plus facts.

- [x] **Step 3: Ground both Nat premises**

Unfold both distinct RHS Nat nodeIds and direct-ground both property wires to `associativityCarrierContent()` with the single `[Plus]` capture. Discharge each grounded base and closure from the cited support facts.

- [x] **Step 4: Produce the public result causally**

Specialize `A(b)` totality at `c` to obtain `Plus(b,c,u)`. Specialize `A(a)` transport with the two public premises and that inner sum to obtain `Plus(a,u,output)`.

- [x] **Step 5: Replace obsolete assembly**

Delete helper-induction and reference architecture, return support/base/public order, and remove the obsolete induction-statements argument from Frege assembly.

### Task 3: Authoritative validation

**Files:**
- Test: `tests/theories/frege.test.ts`

**Interfaces:**
- Consumes: production Frege theory
- Produces: verified ordered arithmetic theorem prefix

- [x] **Step 1: Replay and register all three theorems**

Require canonical forward/backward equality and successful `checkTheorem`/`registerTheorem`.

- [x] **Step 2: Validate causality**

Require independent failure after removing either support citation or either exact Nat grounding action.

- [x] **Step 3: Run repository checks**

Run `npm run typecheck` and the focused Frege theory tests.

- [x] **Step 4: Record completion**

Mark every step complete and append final counts and conformance evidence to the foundation record.

## Completion Evidence

- `associativityCarrierBase`: F44/B33, canonical midpoint 35 regions / 25 nodes / 27 wires.
- `associativityCarrierHereditary`: F83/B84, canonical midpoint 43 regions / 37 nodes / 42 wires.
- `plusAssoc`: F64/B61, canonical midpoint 73 regions / 54 nodes / 69 wires.
- All three theorems replay canonically and register against exactly their preceding production prefix.
- The focused Frege tests pass support-citation ablation, both exact Nat-grounding ablations, obsolete-path exclusion, and exact-prefix replay.
- `npm run typecheck` passes.
