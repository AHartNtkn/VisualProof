# Opt-In Expensive Physics Tests

**Status:** Approved interaction boundary; written for final review

## Outcome

Routine validation must retain all cheap deterministic coverage while avoiding tests whose material assertions require expensive layout settling or long physics simulation. Physics-affecting work and full validation must still have one explicit, authoritative command that runs every expensive case.

## Classification Authority

Expensive tests live under `tests/physics/`. A test belongs there when its material assertion requires one or more of:

- `settle` over a nontrivial fixture;
- large repeated `settleStep` or interactive-physics loops;
- equivalent relaxation whose runtime makes it unsuitable for unrelated changes.

Importing the view engine, testing pure geometry, constructing an engine, or running a small bounded state transition does not by itself make a test expensive. Those tests remain in their existing ordinary suites.

Files that currently mix ordinary and expensive cases are split. This preserves default coverage instead of excluding an entire mixed file for one settling assertion.

## Commands

- `npm test` runs every ordinary test and excludes `tests/physics/**`.
- `npm run test:physics` runs only `tests/physics/**` with the relaxation-appropriate timeout.
- `npm run test:all` runs both authorities.
- `npm run test:watch` watches the ordinary suite; physics remains deliberate.

The Vitest execution policy is shared. Default and physics selection derive from the directory convention rather than separate hand-maintained file lists.

## Migration

Move settle-dominated files into `tests/physics/`. Split mixed files such as application/session or definition tests so only the settling cases move. Preserve test assertions and fixtures; this change alters scheduling and ownership, not physics behavior.

The ordinary configuration no longer needs a global thirty-minute timeout. The long timeout applies only to the physics command.

## Validation

Validation must establish behavior directly:

1. Enumerate or run the ordinary suite and prove it selects no `tests/physics` files.
2. Run the physics command and prove it selects every migrated expensive file.
3. Run the full command and prove both authorities execute.
4. Add an architecture/configuration test that fails if the ordinary suite can select `tests/physics/**` or if the dedicated physics suite selects outside that directory.
5. Preserve typechecking and existing assertions after file moves/splits.

The pre-existing unrelated architecture-layering and session-undo failures are not reclassified as physics failures. If they remain, validation reports them separately rather than weakening either test command.

## Non-Goals

- Excluding all view or physics-module tests from routine validation.
- Reducing settle budgets or weakening physics assertions to make them cheaper.
- Maintaining a duplicate manual exclusion list.
- Changing production physics, rendering, or proof behavior.
