# Single-owner dossier transition

## Outcome

Switching cultures must never show the previous culture's paper, tabs, notes, or
texture beneath the new culture. The previous sheet disappears before animation;
the newly selected sheet alone performs the existing rigid entry motion.

## Ownership model

The folio has exactly one dossier sheet in the rendered tree: `.active-dossier`.
It owns the paper texture, culture tabs, dossier header, record grid, notes, and
status markers. A culture or progression change updates that sheet's content and
then starts its current 260 ms translation-and-shadow timeline.

There is no `.outgoing-dossier`, blank surrogate, duplicate texture, or delayed
removal callback. Rapid culture replacement immediately supersedes the in-flight
sheet and starts the selected culture's entry timeline on the same single owner.
Reduced motion uses the same owner with its non-spatial emphasis; paused motion
projects the selected sheet immediately.

## Removed model

Delete outgoing-sheet cloning and computed-pose capture from the view projection.
Delete outgoing-sheet stacking and styling. Remove tests and evidence assumptions
that require a stationary outgoing sheet or preserve its identity during rapid
replacement. No compatibility selector or dormant clone path remains.

## Unchanged behavior

The dossier timeline remains one coordinator-owned action with the approved easing,
duration, rigid translation, and shadow interpolation. Culture selection authority,
record rendering, cover behavior, record inspection and return, restriction and
packet motion, reset behavior, responsive geometry, and clipping are unchanged.

## Validation

Served-browser tests sample the immediate and intermediate frames of a
Seyric-to-Myratic switch and assert:

- exactly one dossier sheet exists;
- no outgoing dossier exists;
- only the active Myratic header and records paint after selection, while its
  navigation still shows both culture-selection tabs;
- the active sheet retains a translation-only rigid matrix and monotonic travel;
- rapid replacement, reduced motion, and paused motion preserve the same one-sheet
  ownership model.

Canonical screenshots and timeline evidence are regenerated. The complete focused
folio suite, TypeScript check, production build, and diff validation must pass. No
physics code or physics tests are involved.
