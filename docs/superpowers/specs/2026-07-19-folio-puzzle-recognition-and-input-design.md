# Folio Puzzle Recognition and Input Design

## Outcome

Archive records identify their actual puzzles instead of displaying unrelated specimen or mount imagery. Each record shows a complete, zoomed-out rendering of the canonical starting diagram and a culture-local level number. Large collections and large diagrams do not block the interface: previews render in a background worker, persist as derived fingerprint-keyed PNG cache entries, and remain bounded in decoded memory. Hovering or keyboard-focusing a record image exposes a larger inspection preview.

The completion screen accepts Enter and Space as exact equivalents of its sole button. Proof selection no longer removes a selected item on an ordinary click, so an already-selected iterable item remains selected when its drag begins. Shift-click remains the explicit per-item deselection gesture, and a background click remains the explicit clear-all gesture.

This change does not alter proof physics, puzzle content, progression, catalog identity, save semantics, folio motion, or the approved lens and completion styling.

## Controlling interaction rules

- A record preview always depicts the puzzle's canonical starting diagram, never the current attempt or completion state.
- The whole diagram is fitted into the preview without cropping and uses the approved Dark Slate proof palette.
- Level numbers reset for every culture and derive from that culture's folio order. They are presentation, not content or save data.
- Abstract specimen photographs, rubbings, tracings, and hard-coded puzzle-to-image mappings do not remain as fallback preview authorities.
- Completion Enter and Space perform exactly the same controller action as `Return to level selection`.
- Ordinary click on selected content preserves selection.
- Shift-click on selected content deselects that hit without changing the proof item.
- Shift-click on unselected content leaves it unselected.
- With Shift held during a drag, crossed selected hits are deselected and unselected hits remain unselected.
- A still click on actual proof background clears the complete selection.
- Iteration drag, construction claims, and pointer coordinates retain their current ownership and thresholds.
- Proof erasure remains a distinct operation invoked only by Backspace. No pointer selection gesture erases proof content.

## Canonical thumbnail pipeline

### Responsibilities

`PuzzleThumbnailService` is the sole renderer-facing preview authority. It receives a puzzle ID from the folio and obtains the canonical diagram and logical fingerprint from `GameCatalog`. No preview metadata is added to puzzle JSON or catalog prose.

For a cache miss, the service sends this immutable request to one module worker:

```ts
type PuzzleThumbnailRequest = {
  readonly requestId: number
  readonly key: string
  readonly diagram: DiagramJson
  readonly width: 640
  readonly height: 400
}
```

The worker:

1. decodes the diagram through the authoritative diagram decoder;
2. constructs the existing diagram engine;
3. performs seed projection and a fixed, bounded deterministic relaxation budget;
4. fits the complete engine frame into the fixed output rectangle;
5. paints with `DARK`, excluding the generic proof frame just as the production proof canvas does;
6. renders to `OffscreenCanvas`; and
7. returns a lossless PNG blob.

The worker processes one job at a time. Complexity therefore affects only background completion time for one preview, never main-thread input latency or startup mounting.

### Cache identity and bounds

The cache key is:

```text
cursebreaker-thumbnail:<renderer-version>:<logical-fingerprint>:640x400
```

The renderer version changes whenever layout, fitting, output size, or visual semantics change. Catalog names, lore, progression, completion, and guidance cannot invalidate a preview because they do not enter its logical fingerprint.

Two cache levels exist:

- A production IndexedDB store owns derived PNG blobs across launches. It contains no game state and is never a save authority. A failed or missing store degrades to regeneration, not to unrelated imagery.
- An in-memory least-recently-used set owns at most 24 decoded object URLs. Eviction revokes the URL; the persistent PNG remains available without rerendering. The persistent store retains at most 256 entries and removes least-recently-used entries beyond that bound.

The cache is disposable derived data. Corruption, version changes, or deletion cannot affect progression or saves.

### Scheduling and cancellation

The folio registers preview canvases with one `IntersectionObserver`. Records intersecting the scrolling sheet are high priority; a small look-ahead margin queues records approaching visibility. Changing culture or disposing the folio removes obsolete queued requests. A job already executing may finish, but a generation token prevents its result from mounting into a stale record.

While a preview is unavailable, its field reads `Preparing preview…` in the same dark surface. It never shows a generic mount or another puzzle. A failed worker result reads `Preview unavailable` and is retryable after the record leaves and re-enters observation or on the next launch.

## Folio presentation

`FolioRecordProjection` gains `levelNumber`, derived with the one-based index from `catalog.puzzlesInCulture(culture.id)`. The artifact's professional name remains unchanged in catalog data.

The record displays and exposes to accessibility APIs:

```text
<levelNumber>. <professional artifact name>
```

For example, the first Seyric record is `1. The Seyr Ossuary Seal`; the first Myratic record is also level 1 inside the Myratic dossier. Locked-record labels include the same numbered name before their restriction status.

The record's evidence area becomes a neutral dark puzzle-preview aperture. The physical card, artifact name, accession, provenance summary, locked sleeve, priority band, and clearance slip remain. Photograph/rubbing/tracing mount variants and the hard-coded specimen map are deleted.

Hovering the preview aperture or focusing its record displays a larger, pointer-transparent inspection image using the same cached PNG. It disappears on pointer leave, blur, culture change, record drag, or folio disposal. It introduces no menu, button, or navigation delay. A theorem drag uses the same cached PNG in the lifted record.

## Completion keyboard ownership

The production runtime's existing global key owner handles completion shortcuts before proof-only shortcuts:

- mode must be `completion`;
- no transient exists;
- the key must be Enter or Space (`event.key === ' '`);
- Alt, Control, and Meta must be absent; and
- repeated keydown is ignored by the existing repeat guard.

The handler prevents the browser default and dispatches `{ kind: 'levelSelection' }`. This is the same controller path as the button, so save ordering, completion receipt clearing, folio continuity, and archive return cannot diverge. Preventing the default also prevents a focused button from generating a second synthetic click.

## Explicit selection semantics

The shared brush reducer currently infers deselection solely from whether the first hit is already selected and calls that mode `erase`. The misleading name and its application to ordinary clicks are removed. Selection code uses explicit `select` and `deselect` brush modes; `erase` remains reserved for the Backspace proof operation. A brush begin records Shift so click and drag resolution do not have to reinterpret the gesture later.

The reducer follows this table:

| Input | Existing membership | Result |
| --- | --- | --- |
| Ordinary hit click | unselected | add hit |
| Ordinary hit click | selected | preserve hit |
| Shift-hit click | unselected | preserve unselected state |
| Shift-hit click | selected | deselect hit; proof item unchanged |
| Still background click | any selection | clear all |

Drag resolution follows a separate explicit table:

| Input | Brush mode |
| --- | --- |
| Ordinary drag | select crossed hits |
| Shift-drag | deselect crossed selected hits; preserve unselected hits |

Selection and deselection affect only selection membership. No brush mode invokes proof erasure or mutates proof content.

Still releases from domain claims, including the selected-node iteration claim, use ordinary-click semantics and therefore preserve selection. Movement beyond the existing click threshold remains owned by the claim and can complete iteration normally. No rule dispatcher, hit geometry, pointer mapping, or proof step changes.

## Removed preview model

Once the canonical preview is consumed in production, remove:

- `specimenByPuzzle`;
- photograph/rubbing/tracing mount selection and CSS image backgrounds;
- the three current specimen PNG assets;
- the three current mount PNG assets; and
- asset validation and tests that require those obsolete consumers.

Do not add aliases, fallback mappings, placeholder lore art, or checked-in generated thumbnails.

## Validation

### Test-first behavior

Before production edits, focused tests must fail for the absent behavior:

- projection has no culture-local level numbers;
- folio records have no canonical preview request and still consume specimen/mount imagery;
- Enter and Space leave completion unchanged;
- ordinary selected-hit click removes selection;
- iteration drag can lose its selected source.

### Direct validation

- Pure projection tests establish one-based numbering, per-culture reset, and stability under completion/locking.
- Worker tests establish deterministic request/result identity, complete-frame fitting, dark rendering, bounded relaxation, and failure reporting.
- Cache tests establish fingerprint/version invalidation, persistent hits without worker work, queued-request cancellation, generation-token rejection, and both LRU bounds.
- Folio DOM/browser tests establish numbered visible and accessible names, preparing/ready/error states, visible-only scheduling, enlarged hover/focus inspection, theorem-drag reuse, and absence of specimen/mount consumers.
- Completion runtime browser tests exercise Enter and Space independently and assert the same archive state and save transition as the button.
- Brush reducer tests exercise every row in the table and observe the old ordinary selected-hit removal expectation fail before implementation.
- Proof-surface browser tests select an iterable node, ordinary-click it, Shift-click selected and unselected hits without mutating the proof, clear through the background, complete an ordinary iteration drag without selection loss, and prove that Shift-drag deselects crossed selected hits while leaving proof content and unselected hits unchanged.
- Input tests prove Backspace remains the only gesture in this scope that dispatches proof erasure.
- Semantic asset validation proves removed assets have no runtime consumer and retained folio status assets remain valid.
- Type checking, focused unit tests, affected browser tests, the broader non-physics game suite, renderer build, and diff validation pass.

Electron is not launched. The dedicated physics battery is not run because proof physics is unchanged.
