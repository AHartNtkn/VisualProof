# Editor Loupe — Game Asset and Integration Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan task-by-task. Use
> `superpowers:test-driven-development` for production integration and
> `superpowers:verification-before-completion` before claiming completion.

**Goal:** Produce an approval-quality layered editor-loupe asset faithful to the
approved clean mock, then compose it around the main assistant's real circular
construction editor in the game with no game-owned editor interaction.

**Architecture:** Blender produces one coherent hand-loupe construction and
orientation-specific transparent raster layers. A thin HTTP-served review harness
mounts the real production editor and game presentation; it does not duplicate
proof or interaction logic. After visual approval, `editor-loupe.ts` supplies only
DOM layers and measured presentation metrics to the shared main-assistant surface.

**Tech stack:** Blender 4.5.11, transparent PNG, TypeScript 5.5, CSS, Vitest 2,
Playwright 1.60, Vite 5.

## Prerequisites and global constraints

- Do not begin production integration until
  `feature/circular-construction-editor` has been accepted into `main`.
- Merge `main` into `game/cursebreaker-domain`; do not reimplement or cherry-pick
  only parts of the interaction.
- The controlling silhouette is
  `.superpowers/brainstorm/131325-1783786690/content/diegetic-loupe-clean.html`.
  This is a fidelity exercise, not another silhouette exploration.
- The loupe is independent, circular, large, narrow-rimmed, and normally handled
  down-right. It has no persistent title, buttons, toolbar, label, legend, or idle
  connector.
- The current right-click node-spawn popup remains mechanically unchanged.
- The game presentation contains no pointer algorithm, editor state, command map,
  construction semantics, history semantics, or commit/cancel semantics.
- The center of the optics is geometrically flat. Only the outer nonessential
  band may imply refraction or chromatic separation.
- Do not regenerate already-approved desk, gasket, timeline, folio, or substrate
  assets. Consume their approved PNGs as-is.
- Do not add byte-for-byte reproduction tests. Validation concerns dimensions,
  alpha, layer registration, served appearance, and real interaction.
- Do not touch proof physics or run the physics battery in this game-only plan.
- Preserve all unrelated dirty files in the game worktree.

---

## Task 1: Merge the shared main-assistant authority

**Files:** merge result only.

- [ ] **Step 1: Confirm the accepted main commit**

Verify that `main` contains the completed circular editor, frame-shape support,
and presentation seam, and that its completion evidence is green.

- [ ] **Step 2: Merge main into the game branch**

From `game/cursebreaker-domain`:

```bash
git status --short
git fetch origin
git merge main
```

If local unrelated changes overlap, stop and report the exact paths rather than
stashing, restoring, or overwriting them.

- [ ] **Step 3: Validate the merge before game work**

```bash
npm test -- --run tests/app/construction-editor-geometry.test.ts tests/app/construction-editor-surface.test.ts tests/app/comprehension-editor.test.ts
npm run typecheck
```

Expected: the shared editor remains green in the game branch without game code.

---

## Task 2: Build one faithful high-fidelity loupe and focused material studies

**Files:**

- Create: `assets/interface/source/blender/editor-loupe.blend`
- Create: `scripts/assets/render-editor-loupe.py`
- Create: `assets/interface/.staging/editor-loupe-study/`
- Create: `review/editor-loupe-study/index.html`
- Create: `review/editor-loupe-study/style.css`
- Create: `review/editor-loupe-study/evidence/`

**Render contract:**

- orthographic, straight-on output;
- transparent world background;
- one continuous rim/socket/handle construction;
- circular aperture;
- narrow warm-metal rim;
- integrated handle at the approved down-right angle;
- terminal grip visually discreet but clearly reachable;
- one broad approved soft source plus restrained fill, matching the selected
  central-interface lighting rather than the rejected flat or top-hot lighting;
- the same geometry, camera, lighting, and scale across every material study.

- [ ] **Step 1: Model the approved form, not variants**

Construct the rim as a continuous modeled band with a credible lens seat, a
mechanically joined socket, a tapered handle, and one small terminal sizing grip.
Use bevel profiles, subdivision/curvature, and authored surface variation where
they improve the read. Do not assemble visible primitive rings and cylinders or
place the handle on a separate unrelated plate.

Before texturing, render one well-lit clay image over the approved desk/main-lens
composition and critically inspect it against the controlling mock. Correct
silhouette, rim width, aperture size, socket continuity, handle angle, contact,
and grip scale before proceeding.

- [ ] **Step 2: Produce focused material studies on identical geometry**

Render four—not dozens—of materially distinct but plausible treatments using the
same camera and lighting:

1. darkened aged brass with restrained polished contact edges;
2. oxidized bronze with cool recesses and warm worn ridges;
3. blackened instrument brass with sparse exposed gold wear;
4. warm nickel-bronze with a dark wrapped or ebonized handle.

Each study includes the real approved indigo hardwood and central lens beneath it
at expected game scale. No legends appear in the final interface; the review page
may identify variants outside the composition.

- [ ] **Step 3: Serve the study over HTTP**

Serve `review/editor-loupe-study/` with Vite and verify HTTP 200. Present the URL
to the user. Stop production promotion until one treatment or a specific hybrid is
approved.

- [ ] **Step 4: Record the visual decision**

Update the design spec's material paragraph with only the approved treatment and
commit the Blender source, render script, review page, and approved evidence. Do
not promote rejected study PNGs as runtime assets.

---

## Task 3: Render and collect the approved layered runtime assets

**Files:**

- Modify: `assets/interface/source/blender/editor-loupe.blend`
- Modify: `scripts/assets/render-editor-loupe.py`
- Create: `assets/interface/generated/editor-loupe/shadow-{se,sw,ne,nw}.png`
- Create: `assets/interface/generated/editor-loupe/body-{se,sw,ne,nw}.png`
- Create: `assets/interface/generated/editor-loupe/optics.png`
- Create: `assets/interface/generated/editor-loupe/geometry.json`
- Modify: `assets/interface/manifest.json`
- Create: `tests/assets/editor-loupe-assets.test.ts`

**Layer contract:**

1. rear contact shadow;
2. transparent circular aperture reserved for the live canvas;
3. coherent rim/socket/handle body;
4. pointer-transparent symmetric optical edge/reflection layer.

Render at 3072×3072 for the complete instrument, with a measured 2048-pixel
aperture. That supplies at least two source pixels per CSS pixel at the 660-pixel
preferred live aperture while leaving transparent room for the handle and shadow.
The JSON records normalized aperture center/radius, instrument bounds, move-mask
regions, terminal-grip center/radius, and orientation. These numbers are measured
from the final approved render, not guessed in CSS.

- [ ] **Step 1: Write failing asset-contract tests**

Prove every declared PNG exists, is 3072×3072 RGBA with nonempty and nonopaque
alpha, all body layers share the same aperture size, the center aperture is
transparent, optics have `pointer-events: none` when mounted, and
`geometry.json` places each terminal grip inside its image and outside the live
aperture.

Do not assert exact PNG bytes or rerender an approved image in a test.

- [ ] **Step 2: Render orientation-specific layers**

Create south-east, south-west, north-east, and north-west scenes from the same
approved construction. Reposition the modeled handle and lighting/camera rig so
screen-space illumination remains coherent; do not mirror a lit raster in CSS.
Render body and shadow separately with straight alpha. Render one symmetric optics
layer whose central field is transparent/neutral.

- [ ] **Step 3: Inspect registration at native and game scale**

Composite each orientation over the approved desk at 100%, 50%, and its expected
CSS size. Verify no halo, matte fringe, seam, aperture leak, handle detachment, or
shadow discontinuity. Inspect actual pixels with the image viewer as well as the
served browser composition.

- [ ] **Step 4: Publish the approved files without replacing other families**

Add an `editor-loupe` family to the existing manifest while leaving every existing
family and approved PNG untouched. The manifest identifies the selected runtime
files and editable source; it is not a demand to regenerate or compare the approved
pixels during normal validation.

- [ ] **Step 5: Verify and commit**

```bash
npm test -- --run tests/assets/editor-loupe-assets.test.ts tests/assets/manifest.test.ts
npm run assets:validate
git diff --check
git add assets/interface/source/blender/editor-loupe.blend scripts/assets/render-editor-loupe.py assets/interface/generated/editor-loupe assets/interface/manifest.json tests/assets/editor-loupe-assets.test.ts
git commit -m "assets: add approved editor loupe layers"
```

---

## Task 4: Implement the game presentation as a noninteractive adapter

**Files:**

- Create: `src/game/interface/editor-loupe.ts`
- Modify: `src/game/interface/index.ts`
- Modify: `src/game/interface/mount.ts`
- Modify: `app/style.css`
- Create: `tests/game/editor-loupe.test.ts`

**Interface:**

```ts
export function editorLoupePresentation(): ConstructionEditorPresentation
```

The returned object supplies:

- `metrics`, calculated from `geometry.json` and the current CSS aperture diameter;
- a root containing shadow, circular canvas host, body, optics, and transient paint
  slots in that order;
- clear rim/handle elements as `moveTarget`;
- the measured terminal grip as `resizeTarget`;
- geometry-to-CSS projection and lifecycle classes only.

It does not call `addEventListener` for pointer, keyboard, construction, history,
commit, cancel, or spawn behavior. The shared `ConstructionEditorSurface` owns
those listeners.

- [ ] **Step 1: Write failing ownership and structure tests**

Prove:

- the presentation has no editor state and no command callbacks;
- all decorative images have empty alt text, `aria-hidden`, and no pointer events;
- the root has one live canvas host and one resize target;
- presentation metrics are derived from the approved geometry file;
- each `EditorGrip` selects its matching body/shadow pair;
- no title/actions element is mounted in the game presentation;
- the context menu is neither created nor modified here.

- [ ] **Step 2: Verify RED**

```bash
npm test -- --run tests/game/editor-loupe.test.ts
```

- [ ] **Step 3: Implement layered composition**

Use CSS custom properties populated from authoritative geometry:

```css
.curse-editor-loupe__canvas-host {
  position: absolute;
  overflow: hidden;
  border-radius: 50%;
}
.curse-editor-loupe__optics,
.curse-editor-loupe__body,
.curse-editor-loupe__shadow {
  position: absolute;
  inset: 0;
}
.curse-editor-loupe__optics { pointer-events: none; }
```

The live canvas fills the measured circular aperture exactly. Do not round a
rectangular texture under it or add a second CSS mask that disagrees with the
shared editor geometry.

- [ ] **Step 4: Add set-down/lift presentation**

Opening uses a short vertical offset, shadow convergence, and restrained optical
settling. Closing uses the inverse lift. Input and focus are live at the final
authoritative geometry immediately; semantic disposal happens before the visual
exit. Under `prefers-reduced-motion`, use opacity/shadow only.

- [ ] **Step 5: Thread the presentation into the real proof front**

In `mountCursebreaker`, pass `editorLoupePresentation` through the shared
`ProofFrontViewport` presentation option. Do not branch `ComprehensionEditor`, add
a game resize handler, or create a second editor instance.

Ensure existing body-level `.vpa-menu`, active cross-surface gesture SVG, and
`.curse-refusal` paint above the optics. Do not change the popup's contents or
behavior.

- [ ] **Step 6: Verify and commit**

```bash
npm test -- --run tests/game/editor-loupe.test.ts tests/app/construction-editor-surface.test.ts tests/app/comprehension-editor.test.ts
npm run typecheck
git diff --check
git add src/game/interface/editor-loupe.ts src/game/interface/index.ts src/game/interface/mount.ts app/style.css tests/game/editor-loupe.test.ts
git commit -m "feat(game): present construction editor as loupe"
```

---

## Task 5: Build an HTTP review harness around the real production editor

**Files:**

- Create: `review/editor-loupe/index.html`
- Create: `review/editor-loupe/main.ts`
- Create: `review/editor-loupe/style.css`
- Create: `review/editor-loupe/evidence/`
- Create: `tests/review/editor-loupe-browser.test.ts`
- Create: `scripts/capture-editor-loupe.mjs`

The harness imports the production `ProofFrontViewport`, production
`ComprehensionEditor`, production game presentation, and an existing comprehension
fixture. It contains no alternate geometry, pointer behavior, or proof logic. Its
only job is to put the actual production editor over the approved desk/main-lens
composition at controlled viewport/invocation positions.

- [ ] **Step 1: Write failing served-browser contracts**

At 1600×1000, 1920×1080, and a supported narrow viewport, prove:

- the live aperture is circular and equal-width/equal-height;
- preferred diameter is 660 CSS pixels when space permits and minimum is 420;
- down-right is selected when reachable;
- edge positions select a stable alternate orientation and keep the terminal grip
  reachable;
- canvas pixels and pointer hit targets agree at center and near the boundary;
- rim dragging and grip resizing are smooth and shared geometry remains the only
  size state;
- right-click opens the existing spawn popup above the optics;
- an active host-to-draft gesture and a pointer-local red refusal are unclipped and
  above the loupe;
- no persistent title, buttons, toolbar, legend, label, or idle connector exists;
- open/close and reduced-motion transitions do not delay input or semantic close.

- [ ] **Step 2: Implement the thin harness and verify RED becomes GREEN**

```bash
npm test -- --run tests/review/editor-loupe-browser.test.ts
```

- [ ] **Step 3: Capture review evidence**

Generate deterministic screenshots for:

- preferred south-east pose;
- minimum diameter;
- each viewport-edge orientation;
- active cross-surface gesture;
- open, settled, and closing moments;
- reduced motion;
- existing spawn popup;
- pointer-local red thought bubble.

Serve the final page over HTTP and present its URL to the user. This is the first
approval gate for the complete live composition, not a substitute interactive
implementation.

- [ ] **Step 4: Apply only approved visual corrections**

If visual evidence exposes material, registration, lighting, optics, or motion
problems, correct the authoritative asset/presentation owner. Do not compensate
with offsets in the harness or alter editor mechanics.

- [ ] **Step 5: Commit approved review evidence**

```bash
git add review/editor-loupe tests/review/editor-loupe-browser.test.ts scripts/capture-editor-loupe.mjs
git commit -m "review: demonstrate production editor loupe"
```

---

## Task 6: Final integration validation and handoff

- [ ] **Step 1: Run relevant validation**

```bash
npm test
npm run typecheck
npx playwright test e2e/cursebreaker.spec.ts
npm test -- --run tests/review/editor-loupe-browser.test.ts
npm run assets:validate
git diff --check
```

Do not run `npm run test:physics`; this plan changes presentation only after the
shared main-assistant geometry has already been validated.

- [ ] **Step 2: Prove no competing path exists**

Search and inspect to confirm:

- the game has no move/resize pointer listeners for the loupe;
- there is no game-owned editor size state;
- there is no rectangular editor compatibility CSS;
- there is no baked diagram image;
- the right-click spawn popup still comes from `SpawnCascade`;
- title/actions are absent only through the game presentation, not through a new
  command path.

- [ ] **Step 3: Request independent review**

Use `superpowers:requesting-code-review`. The reviewer checks visual layer
registration, shared interaction ownership, exact pointer mapping, edge
reachability, popup preservation, reduced motion, and absence of duplicated
editor logic. Fix all Critical and Important findings and rerun affected evidence.

- [ ] **Step 4: Append conformance and push**

Append the completed game responsibilities, asset paths, displaced rectangular
presentation, merge source, validation results, HTTP evidence URL/path, and user
visual approval to the foundation record. Push `game/cursebreaker-domain` after
all commits are present.
