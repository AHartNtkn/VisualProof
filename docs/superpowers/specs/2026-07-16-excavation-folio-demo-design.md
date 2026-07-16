---
name: excavation-folio-demo
created: 2026-07-16
status: ready-for-user-review
---

# Excavation Folio Library Demonstration

## 1. Purpose

Build a standalone, high-fidelity demonstration of the excavation-folio concept as a possible replacement for Cursebreaker's library interface. The demonstration must convey the intended final visual quality, physical organization, information hierarchy, state language, and motion. It is an evaluation artifact, not an application integration.

The approved central lens, corrected chassis, timeline, Natural-indigo hardwood desk, and selected E substrate remain the visual authority for scale, lighting, palette, and available workspace. The folio occupies the left side of that composition without shrinking, covering, or visually competing with the lens.

## 2. Responsibility boundary

The demo owns:

- a substantial modern conservation folio;
- culture tabs and stacked culture dossiers;
- artifact records and their mounted specimen imagery;
- professional catalog information and provenance;
- physical expressions of availability, completion, importance, and restriction;
- culture-specific artifact and documentary evidence within one institutional archive system;
- dossier, record, packet, and cover animations;
- a standalone inspection state;
- responsive positioning beside the approved lens;
- keyboard-only review controls for selecting simulated progression states;
- captured still and motion evidence.

The demo does not own:

- proof interaction or proof rendering;
- puzzle loading;
- real unlock or completion calculation;
- save data or persistence;
- broken-seal reference manifestation or dissolution;
- teacher presentation;
- broken-seal reference behavior beyond the demonstrated physical artifact states;
- integration with `src/game`, `src/app`, or either application mount;
- file/folder importing, loading, unloading, conflicts, or any other source-management behavior from the proof assistant.

## 3. Demonstration content

Use the current opening catalog as authored content, copied into a small demo-only projection rather than imported from runtime modules.

### Seyric evidence

Represent all six initial artifacts as the opening content fixture. Six is the
ordinary visible density at the approved viewport, not a culture capacity:

1. The Seyr Ossuary Seal
2. Seyr Cairn Seal IV
3. The Orra Gate Fragment
4. Tel Vey Chamber Seal VIII
5. The Auten Reliquary Closure
6. Seyric Field Seal S-27

The Seyric records communicate the oldest securely excavated sealing horizon through their evidence content:

- stone rubbings, edge tracings, and restrained monochrome specimen photographs;
- excavation notes and accession history;
- conservation repairs visible on the recorded or mounted objects;
- chronological uncertainty expressed through revisions to catalog information;
- little overt mystical decoration.

### Myratic evidence

Represent the first artifact:

- The Uninscribed Votive of Myrat

The Myratic records use the same institutional folio, mounts, labels, and status language as the Seyric material. Their evidence content differs:

- survey photographs, tracings, and transcriptions recording repeated empty apertures;
- registration and alignment evidence found on or inferred from the artifacts;
- the material colors and markings of the actual finds;
- evidence of scholarly uncertainty and isolation;
- a participatory quality documented in the construction of the finds, without presenting the tradition as merely “the existential culture.”

Production culture dossiers must support dozens of records without changing this
record scale or creating another catalog location. The demonstration's next motion
revision must therefore include a realistic long-culture fixture in addition to
the permanent opening records.

### One institutional visual language

The folio is not reskinned by culture. Every culture uses the same:

- dossier stock and binding system;
- catalog labels and typography;
- record sizes and mount families;
- tabs and navigation;
- status treatments;
- inspection mechanics and animations.

The archive may use a small reusable set of evidence mounts—such as photograph, rubbing, tracing, fragment, transcription, or material sample—but each mount type is available to every culture. Adding a culture requires new artifact evidence and catalog content, not a new interface style.

## 4. Folio construction

The folio is a large working conservation object, not a rectangular application panel.

Required visible construction:

- dark cloth, leather, or archival-board exterior;
- believable thickness and layered page edges;
- a hinged cover or guard leaf;
- reinforced spine or binding structure;
- two visible culture tabs;
- a stack of dossiers with readable depth;
- mounts, hinges, fasteners, labels, and protective overlays at plausible scale;
- slight wear concentrated at handled edges;
- directional light consistent with the approved central instrument.

The folio may extend partially beyond the left viewport edge, as though it has been placed within reach. It must not be tilted as an entire interface plane. Small physical pieces may be slightly askew.

The default composition at 1600×1000 must retain the corrected central instrument at full viewport height. The folio occupies the remaining left desk region and may overlap the chassis shadow, but it must not cover the lens aperture, brass aperture plate, or timeline.

## 5. Artifact record grammar

Every artifact record is a coherent archival object with:

- one specimen representation: rubbing, photograph, tracing, fragment diagram, or mounted material sample;
- professional name;
- one optional accession or location line;
- one brief descriptive line conveying provenance, physical function, or curator shorthand.
- a physical status treatment.

Formal theorem text is absent from the primary record face. The archive describes artifacts, not mathematical exercises.

The player-facing content budget is one image and no more than three short text lines per artifact. A culture may also have one short shared introductory note. Artifact records do not contain essays, multi-paragraph lore, or multiple documentary images.

### Continuous magical sheet

Each culture dossier contains one continuous vertically scrolling magical sheet.
The folio opening is a viewport onto that sheet and normally exposes roughly six
records in the approved two-column density. Additional records continue below; no
page boundary, page-turn control, numbered leaf, sub-dossier, or pagination model
exists.

Wheel, trackpad, touch, and standard keyboard scrolling move the sheet directly.
The folio body, culture tabs, and dossier identity remain fixed while the sheet
travels beneath them. A partial continuation at the lower viewport edge makes the
overflow discoverable without a visible software scrollbar or explanatory legend.
Scrolling is continuous and does not snap to six-record increments.

Artifact order is deterministic and unaffected by unlocking, completion, replay,
or broken-seal reference availability. Each culture retains its own scroll position
while the folio is open. Inspection returns to the exact prior position. Switching
cultures and returning restores that culture's prior position rather than resetting
to the top. Focus order follows the same stable artifact order. Reduced-motion mode
removes inertial flourish but preserves direct scrolling and position restoration.

### Status treatments

Statuses must be readable without relying on color alone or game icons.

- **Available:** record face exposed; pull edge or mount accessible.
- **Completed:** record remains usable and receives a restrained clearance annotation, conservation slip, or dated examiner mark. No checkmark, star, trophy, or glow.
- **Required gateway:** more extensive documentation, chain-of-custody band, or institutional priority tab. It must not resemble a “main quest” badge.
- **Elective:** smaller or less prominent record with ordinary catalog treatment; still fully credible archival material.
- **Inaccessible:** the record's existence is visible, but useful content is covered by an unopened envelope, tied guard, folded backing, restricted sleeve, or untranslated slip. It must not be a grey disabled card or padlock icon.

The demo must show at least one artifact in every status.

## 6. Information hierarchy

At rest, the player should read:

1. which culture dossier is forward;
2. which artifact records are physically accessible;
3. which record is currently selected or handled;
4. the selected artifact's professional name and material character.

Lifting a record makes the same compact image and text easier to inspect. It does not reveal additional lore, a reverse-side essay, a folded explanatory note, or expanded catalog prose. Relationships between finds may be suggested by their arrangement or a terse accession notation, not explained through dependency arrows or cross-reference paragraphs.

## 7. Interaction model

These interactions exist only to demonstrate the folio:

- selecting a culture tab brings its dossier forward;
- selecting an available or completed artifact lifts its record into inspection;
- selecting an inaccessible artifact produces a short physical refusal—its tie, cover, or sleeve resists and settles back—without a software error message;
- dismissing inspection returns the record to its mount;
- a restricted packet can be demonstrated opening when review state changes;
- the folio cover or guard leaf can open and close;
- a dossier can shift enough to expose the one beneath it.

The central lens is inert in this demo.

Visible player-facing controls must be physical parts of the folio. Review-only controls are keyboard shortcuts with no visible strip, button, help overlay, or legend in the demo. They switch among named simulated progression states, toggle full/reduced/paused motion, close inspection, and reset the demo. Their mapping is documented for reviewers and automated capture outside the visible interface.

## 8. Motion language

Motion must communicate weight, friction, attachment, and layering.

- **Cover:** rotates around a stable hinge with slight settling; no generic fade or scale animation.
- **Culture dossier:** translates and lifts through a short stacked-paper movement; underlying sheets compress or shift subtly.
- **Tab:** moves with its dossier and may flex or lag slightly, but does not bounce like a button.
- **Artifact record:** first releases from corners or a mount, then lifts and translates. Its shadow and focus change follow its height.
- **Folded note or overlay:** opens around an authored crease or registration hinge.
- **Restricted packet:** tie or guard moves in an ordered sequence; nothing dissolves or simply disappears.
- **Return:** reverses the physical action with a slightly faster, controlled settling phase.

Animations must be interruptible without leaving layers in contradictory states. Reduced-motion mode preserves state transitions through short crossfades and depth changes while removing large rotations and translations.

## 9. Visual asset standard

All visible folio components must be authored assets or deliberate CSS/canvas constructions with material detail. Prohibited shortcuts:

- flat rounded rectangles presented as paper;
- uniform noise pasted over every material;
- generic drop shadows unrelated to object height;
- stock UI icons;
- emoji;
- fake handwriting fonts used indiscriminately;
- placeholder photographs;
- identical record templates with only text changed;
- glowing outlines for selection;
- large labels explaining the status vocabulary.

Assets may be generated procedurally, painted, composited from CC0 sources with retained provenance, or rendered from simple 3D constructions where that materially improves credibility. The final demo must remain a 2D browser composition.

## 10. Technical shape

The demo lives under `review/excavation-folio/` and is served independently by Vite. It uses:

- semantic HTML for the physical object hierarchy;
- CSS custom properties and transforms for layout and motion;
- TypeScript only for the demo state machine, pointer/keyboard handling, and review controls;
- image assets under `assets/interface/generated/excavation-folio/`;
- source and provenance records under `assets/interface/source/inputs/excavation-folio/`;
- no imports from `src/app`, `src/game`, `src/kernel`, or `src/view`.

The demo state is a closed review model:

```ts
type ReviewProgression =
  | 'arrival'
  | 'seyric-open'
  | 'seyric-practiced'
  | 'seyric-cleared'
  | 'myratic-released'

type FolioState = {
  culture: 'seyric' | 'myratic'
  inspectedArtifact: string | null
  cover: 'open' | 'closed'
  progression: ReviewProgression
  motion: 'full' | 'reduced' | 'paused'
}
```

This state is demonstration data only. It is not designed as a future runtime API.

## 11. Required review scenarios

The finished demo must provide deterministic paths and captures for:

1. closed folio beside the approved lens;
2. default open Seyric dossier;
3. Seyric mixed state showing available, completed, gateway, elective, and inaccessible records;
4. lifted Seyric artifact inspection with provenance visible;
5. inaccessible artifact resistance animation;
6. Myratic dossier brought forward;
7. Myratic restricted packet before release;
8. Myratic packet opened after simulated release;
9. reduced-motion culture switch and record inspection;
10. 1600×1000 and 1920×1080 compositions without lens obstruction.

## 12. Validation

Automated validation must prove:

- the demo imports no application or domain runtime;
- no visible developer controls or shortcut legend exist;
- keyboard review shortcuts reach every simulated progression and motion state, close inspection, and reset the demo;
- all named scenarios are reachable;
- culture switching, cover state, inspection, restriction, and review-state changes settle into deterministic DOM states;
- reduced motion removes large mechanical travel but preserves legibility;
- the lens aperture and timeline are never overlapped by folio hit regions;
- all required artifact names and provenance summaries appear in the demo projection;
- status semantics include a non-color physical cue;
- screenshots exist for the required still scenarios;
- a recorded trace or frame sequence demonstrates each required animation family.

Human visual review remains authoritative for whether the concept feels convincing enough to pursue.
