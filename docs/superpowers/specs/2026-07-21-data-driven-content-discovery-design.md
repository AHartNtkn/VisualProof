# Data-Driven Content Discovery Design

## Outcome

Adding or removing a complete manifest-owned puzzle bundle changes content only. The renderer, tests, and packaged desktop game automatically bundle the available runtime JSON files; no per-puzzle TypeScript import or map entry exists.

`content/manifest.json` remains the sole registration and ordering authority. Discovery makes files available to the loader but does not register them. A discovered file absent from the manifest is inert at runtime.

## Scope

This reconstruction owns:

- build-time discovery of runtime content JSON;
- the `gameContentFiles` production inventory;
- Vite/Vitest typing for that discovery;
- tests and content-format documentation that currently require static imports;
- renderer and desktop validation of manifest-only content additions.

It does not redesign manifest version 3, `loadGameContent`, catalog semantics, progression, coverage, guidance, validation sidecars, content schemas, proof behavior, or puzzle presentation.

## Complexity Ledger

### Essential behavior and state

- The manifest selects runtime files and determines puzzle order.
- `loadGameContent(files)` synchronously validates and assembles an immutable catalog.
- Missing manifest-owned files fail with the exact missing path.
- Tests may inject synthetic `GameContentFiles` records without Vite or filesystem access.
- Coverage and validation sidecars remain build-only.

### Derived data to stop authoring

`gameContentFiles` is an availability inventory derivable from the runtime content directory. Its current 113 import bindings and 113 repeated keys are not domain state.

### Prohibited power

Renderer and game code receive no Node, filesystem, Electron, IPC, network, or runtime fetch authority. Content discovery occurs during Vite transformation.

### Deletion target

Delete every individual JSON import and every handwritten per-file key from `src/game/content/files.ts`. Delete documentation and tests that require authors to synchronize a static registry. Do not replace them with generated committed source or a compatibility map.

## Target Architecture

`src/game/content/files.ts` owns one eager `import.meta.glob` call over positive runtime-only patterns:

- `content/manifest.json`;
- `content/puzzles/**/*.json`;
- `content/definitions/**/*.json`;
- `content/progression/**/*.json`;
- `content/catalog/**/*.json`;
- `content/guidance/**/*.json`.

The module requests each JSON module's default export eagerly, strips the fixed `../../../content/` prefix from Vite's module key, constructs a `GameContentFiles` record, and freezes it. It does not glob `coverage`, `validation`, or `schemas`.

The public `gameContentFiles` export remains unchanged. `loadGameContent(files)` remains pure, synchronous, bundler-independent, and injectable. Its manifest parsing and missing-file checks remain the semantic authority.

`tsconfig.json` includes `vite/client` types so `ImportMeta.glob` is typechecked. The Electron compilation remains isolated through `tsconfig.electron.json`, which supplies its own types.

## Data Flow

1. Vite or Vitest discovers the allowed runtime JSON modules at transform time.
2. `files.ts` normalizes discovered module keys into manifest-relative paths.
3. `gameContentFiles` exposes the immutable availability record.
4. `loadGameContent` reads `manifest.json` from that record.
5. The loader selects only manifest-named files, preserving manifest order and ignoring unmanifested inventory entries.
6. The renderer constructs the catalog synchronously as it does now.
7. Electron packages the already-built renderer; no desktop filesystem lookup is introduced.

## Failure Semantics

- A manifest-owned path missing from the discovered inventory retains the current path-specific `GameDomainError`.
- Malformed JSON or invalid content retains current loader and build-validation failures.
- Unmanifested runtime JSON is ignored by the runtime catalog. Build-only validation remains responsible for complete authoring-bundle checks.
- There is no fallback catalog, stale generated registry, skipped file, or runtime discovery retry.

## Tests and Validation

TDD begins from the present failure: the manifest contains the twelve new Seyric paths while the handwritten registry does not, so production catalog tests fail at the first missing path.

The replacement adds direct behavior evidence that:

- every manifest-owned runtime path is present in `gameContentFiles`;
- all current manifest puzzles load without per-puzzle source registration;
- runtime discovery excludes coverage, validation, and schemas;
- injected fixture maps and exact missing-path errors remain unchanged;
- production source contains no individual puzzle JSON imports or handwritten puzzle registry entries.

Authoritative validation includes content validation, catalog/content/progression tests, architecture boundaries, typecheck, renderer build, desktop build, and desktop startup. The current twelve content bundles are the real integration case: they must become game-loadable without adding their IDs or paths to TypeScript.

## Rejected Alternatives

- A generated registry retains derived source state and adds generation ordering to tests, builds, and commits.
- Runtime fetch requires asynchronous catalog startup and conflicts with the renderer's `connect-src 'none'` policy.
- Electron or Node filesystem discovery expands IPC and security authority into a content problem.
- A custom Vite virtual-module plugin duplicates functionality already provided by source-level eager globbing and requires parallel Vite/Vitest configuration.

## Success Standard

The manifest and content files are the only authored puzzle inventory. Adding the next complete puzzle bundle requires no change outside `content/`, and the filesystem validator, test runtime, renderer build, and desktop build all consume it successfully.
