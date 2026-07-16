# Task 2 report — institutional excavation folio assets

## Outcome

Implemented the reusable institutional folio asset family, seven distinct artifact specimen images, and static Seyric/Myratic dossier compositions. Task 3 motion was not implemented.

## Asset methodology

- `scripts/assets/build-excavation-folio-assets.py` uses Pillow and fixed random seeds to produce deterministic RGBA PNGs.
- Materials are authored by role rather than receiving one generic overlay: cloth/leather shell weave and reinforced spine, fibrous dossier stock, evidence-specific mount construction, handled-edge wear, registration fasteners, archival sleeve folds, clearance annotation, and chain-of-custody priority band.
- The nine reusable institutional assets share a warm upper-left light assumption, common archival scale, restrained brass/umber hardware, and conservation-paper palette.
- Each artifact specimen is independently drawn from its catalog evidence:
  - ossuary seal: repaired radial stone seal;
  - cairn seal: edge-traced field plate;
  - gate fragment: mortared broken closure fragment;
  - chamber seal: monochrome abrasion/join survey plate;
  - reliquary closure: fiber-bearing plate with red mineral residue;
  - field seal S-27: dense comparative rubbing;
  - Myratic votive: aligned empty apertures and registration lines.
- The DOM maps each Task 1 artifact id directly to one generated specimen. `folio.css` uses the same dossier, mounts, labels, tabs, and status language for Seyric and Myratic content.

## Provenance

- All output is locally procedural; no external or borrowed imagery is used.
- Machine-readable provenance: `assets/interface/source/inputs/excavation-folio/provenance.json`.
- The provenance lists the generator, methodology, empty external-source list, and all sixteen outputs.

## TDD evidence and exact validation

Red:

`npm test -- tests/review/excavation-folio-assets.test.ts`

- Result: exit 1, 5/5 tests failed for the intended missing asset family, missing provenance, missing `folio.css`, and absent specimen mapping.

Green:

`npm test -- tests/review/excavation-folio-assets.test.ts`

- Result: exit 0, 1 file passed, 5 tests passed.

Final focused validation:

`npm test -- tests/review/excavation-folio-assets.test.ts tests/review/excavation-folio-model.test.ts`

- Result: exit 0, 2 files passed, 30 tests passed.

`npm run typecheck`

- Result: exit 0, `tsc --noEmit` produced no diagnostics.

The asset tests directly validate required files, minimum dimensions, non-placeholder byte sizes, RGBA color type for composited pieces, seven distinct SHA-256 specimen hashes, complete procedural provenance, specimen DOM mapping, stylesheet loading, all five physical status selectors, and absence of disabled/grayscale/glow treatments.

## Visual inspection evidence

The demo was served with Vite and captured through Chromium at an exact 1600×1000 viewport.

- Initial default inspection: `/tmp/excavation-folio-task2-1600x1000.png`
- Initial mixed status: `/tmp/excavation-folio-task2-mixed.png`
- Corrected mixed status: `/tmp/excavation-folio-task2-final-corrected.png`
- Myratic released dossier: `/tmp/excavation-folio-task2-final-myratic.png`
- Final post-correction verification: `/tmp/excavation-folio-task2-final-verified.png`

Inspection confirmed:

- folio remains entirely left of the aperture boundary and does not cover the lens or timeline;
- specimen forms are immediately distinguishable and materially consistent;
- completed slips, gateway band, accessible pull edge, smaller elective record, and restricted sleeve read as physical treatments without icon dependence;
- Myratic uses the identical institutional page and mount grammar;
- each face stays within the one-image/three-line content budget.

The first mixed render used three columns and clipped the third record column against the lens-safe workspace. It was corrected to two columns. Subsequent inspection showed the six Seyric records legibly arranged in three rows; row height was tightened once more to retain the final text lines inside the 1000px viewport.

## Commit

- Implementation commit: `a000dc5` (`feat(review): build excavation folio asset system`)
- This report is committed separately so it can record the immutable implementation hash.

## Self-review

- Scope is limited to Task 2 assets, provenance, asset tests, specimen mapping, and static folio styling.
- No state-machine, keyboard-control, animation, transition, or Task 3 motion behavior was added.
- Existing unrelated dirty central-lens, desk, substrate, interface-static, plan, and spec files were not staged or modified by this task.
- The generated assets are reproducible from a single source script and do not depend on network resources.
- The current visual grammar is intentionally restrained and institutional. Culture identity is carried only by artifact/documentary content.

## Concerns

- The central lens/desk assets consumed by the Task 1 composition are unrelated dirty worktree inputs; this task intentionally does not claim or commit them.
- Fine catalog text is designed as secondary texture at the full composition scale; record lifting/inspection in Task 3 will provide the intended easier reading state.
