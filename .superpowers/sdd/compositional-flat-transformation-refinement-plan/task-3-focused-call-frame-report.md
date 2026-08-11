# Task 3B0 focused compiler call-frame report

## Status

Complete. Every `CompiledSite` now derives one exact source compiler call at
the endpoint of its existing focus. The result is either the checked open
root call or the precise nested `compileRegion?` call that produced the
focused annotated body.

## Implemented boundary

### Endpoint frame

`VisualProof/Concrete/Elaboration/Compiled.lean` defines
`RegionCallFrame d body` with exactly two constructors:

- `root` owns the ambient and local wire contexts plus one successful
  `compileRoot? d ambient locals = some body` equation;
- `nested` owns the fuel, origin, exact `WireContext`, exact
  `BinderContext`, and one successful
  `compileRegion? d fuel origin context binders = some body` equation.

The body's origin, wire count, and relation context are dependent indices.
`FocusedRegionCallFrame` existentially exposes those hidden endpoint indices
and the same annotated body; it adds no equality, path, or ancestor data.

### Synchronized source inversion

One private mutual definition synchronizes the successful source computation
with the existing `CompiledRegionFocus`/`CompiledItemsFocus`:

1. The root entry unfolds `compileRoot?` once. The nested entry unfolds the
   supplied `compileRegion?` once.
2. Each entry extracts the exact successful direct-occurrence computation
   whose output is indexed by the focused compiled region.
3. A `.tail` focus inverts one ordered occurrence step and continues with the
   exact suffix equation.
4. A `.cut` or `.bubble` focus identifies the selected child from the
   successful occurrence equation, extracts the exact recursive
   `compileRegion?` equation, and continues with the already stored nested
   focus.
5. A `.here` focus returns the supplied root or nested frame unchanged.

The recursion is only over the existing focus. It does not search source
occurrences or regions, construct a second focus, or accumulate frames.

### Canonical root authority and public projection

`CheckedOpen.compilation_computation` states directly that the actual
canonical call

```lean
compileRoot? checked.val.diagram checked.val.exposedWires
  checked.val.hiddenWires
```

returns `some checked.compilation`. Its proof is derived from the existing
`CheckedOpen.elaborate_body_computation` authority.

`CompiledSite.callFrame` applies the private synchronized inversion to exactly
that canonical equation and `CompiledSite.focus`. `CompiledSite` still stores
only its original `focus` field.

## Mathematical claim established

For a checked open source compilation and an existing focus into that exact
annotated result:

- a focus ending at the open root yields the original successful root call;
- a focus ending below the root yields the exact fuel, wire context, binder
  context, and successful nested-region call whose result is the focused
  annotated body;
- the endpoint body is definitionally the body selected when the synchronized
  inversion reaches `.here`, so no reconciliation equality or cast is needed.

## Responsibility-model self-review

### Essential state and invariant

- The sole canonical annotated source compilation remains
  `CheckedOpen.compilation`.
- The sole navigation authority remains `CompiledSite.focus`.
- A call frame owns one successful compiler call and its necessary concrete
  inputs. It owns no parent or child frame.
- The compiler equation's right-hand body is the same dependent body carried
  by the returned frame.

### Derived data

- Root versus nested endpoint kind is derived by following the focus.
- Nested fuel, wire context, binder context, and success equation are derived
  by synchronized inversion.
- `CompiledSite.callFrame` is a function, not a stored field.
- Existing route, intrinsic context, body, depth, direct items, and selection
  factorization continue to derive from the same focus.

### Forbidden authority audit

- No frame list, recursive trace, second route, second path, source search,
  stored equation, equality field, cast layer, or compiler replay authority
  was added.
- No target diagram, target compiler call, target focus, transformation map,
  receipt, endpoint replacement, callback, fold algebra, or simulation record
  appears in this slice.
- The only public call-frame declarations are the two-constructor dependent
  frame, its dependent endpoint abbreviation, and
  `CompiledSite.callFrame`. All synchronized inversion helpers are private.

## Line-count self-review

The implementation adds 178 Lean lines:

- 10 lines in `Compile/Elaborate.lean` for the direct canonical root equation;
- 168 lines in `Compiled.lean` for the dependent frame, endpoint package,
  one private mutual inversion, and the public projection.

Of the 168 focus-module lines, 137 implement the mutually recursive dependent
inversion and its unavoidable impossible branches. The remaining 31 lines are
the public types, documentation, and projection. The implementation adds no
parallel compiler or navigation module and keeps all proof machinery beside
the focus it eliminates.

## Validation

All required checks passed:

- strict warning-as-error checks for
  `Concrete/Elaboration/Compile/Elaborate.lean`,
  `Concrete/Elaboration/Compiled.lean`,
  `Concrete/Elaboration.lean`, and `Concrete/Encode.lean`;
- focused builds of `Concrete.Elaboration.Compile.Elaborate`,
  `Concrete.Elaboration.Compiled`, and `Concrete.Encode`;
- full `lake build` (96 jobs);
- `scripts/audit-lean-authority.sh implementation`;
- `scripts/audit-lean-authority.sh documentation`;
- focused scans for `sorry`, `admit`, `#check`, and synthetic `example`
  declarations in both changed Lean modules;
- focused declaration scans confirming one call-frame authority and the
  existing single derived route authority;
- `git diff --check`.

Every changed module and required aggregate is warning-free under
`-DwarningAsError=true`. The full build succeeds.

## Concerns

None within Task 3B0. The frame remains endpoint-only and the fail-fast
fallback was not required.
