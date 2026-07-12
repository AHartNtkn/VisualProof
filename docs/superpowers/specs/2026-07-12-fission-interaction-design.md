# Fission pull-out interaction design

## Outcome

Players can factor any kernel-valid syntactic occurrence out of a rendered term node by pulling that occurrence's anatomy outward. The same interaction is available in Edit and Proof. Internal anatomy highlighting identifies fission; a halo enclosing the whole node or selected subgraph identifies iteration. Holding Ctrl categorically reserves the gesture for existing physics dragging.

## Rule exposed

For a term node containing context `C[s]`, fission at the occurrence path of `s`:

1. requires `s` to be closed with respect to binders outside `s`;
2. replaces that occurrence with a fresh free port `q` in the residual node `C[q]`;
3. creates a producer node containing `s` in the host node's region;
4. connects the producer output to the residual node's `q` port with a fresh wire; and
5. preserves the original wires of every free port used by `s`.

The rule is polarity-blind and is the exact inverse of fusion along the fresh wire. The user interaction exposes every path accepted by the kernel, including the root path. It does not silently replace an invalid chosen occurrence with a larger valid one.

## Path-aware term anatomy

The rendered term anatomy must retain syntactic-occurrence identity instead of erasing paths after layout. Each term occurrence has:

- its exact `PathSeg[]` from the node root;
- a consumer-facing hit trace lying on the painted anatomy;
- the set of painted anatomy primitives belonging to the occurrence; and
- its syntactic depth for deterministic overlap resolution.

Application children use the output carrier entering their parent application as their hit trace. Lambda bodies use the body output carrier immediately inside the binder boundary. Leaves use their own carrier stem. The root uses the internal output run before the external wire begins. No new permanent handle or glyph is drawn.

Highlight primitives comprise the occurrence's internal bars and stems plus its consumer-facing carrier. Root highlighting therefore covers all internal anatomy but not the enclosing node boundary. Identical subterms at different paths retain distinct occurrence identities.

Tromp layout is the provenance authority. Bending maps its path-tagged primitives into world geometry without guessing paths from angles after the fact. Static engine geometry carries the resulting occurrence records. Conversion animation disables input already; intermediate morph geometry need not expose interactive occurrences, and the rebuilt final engine restores authoritative path metadata.

## Shared gesture arbitration

One `FissionDragController` is used by Edit construction, the main proof track, and both fixed proof fronts. Gesture ownership is resolved in this order:

1. When Ctrl is held, fission neither highlights nor claims; viewport physics retains its existing behavior.
2. An actual wire stroke or terminal halo is owned by the existing connection controller.
3. A term-occurrence hit trace is owned by fission.
4. Elsewhere on a selected Proof node or subgraph, existing iteration remains available.
5. Otherwise existing selection behavior continues.

Shift-modified selection gestures are not claimed by fission. A still primary click through a fission locus remains an ordinary selection click and makes no diagram change.

Within the fixed device-pixel hit tolerance, the nearest occurrence trace wins. Exact distance ties choose the deeper syntactic path, then lexicographic path order. Legality is evaluated after identity selection: an illegal deeper occurrence previews red rather than falling through to a legal ancestor.

## Highlight and drag feedback

Passive hover over an occurrence trace highlights only that occurrence's anatomy:

- valid candidate: the existing valid green;
- binder-dependent or otherwise invalid candidate: the existing refusal color.

This internal highlight is never accompanied by an enclosing halo. Conversely, iteration highlights the complete selected node or subgraph with an enclosing halo and never singles out internal anatomy.

Once the pointer crosses outside the host node boundary, fission additionally previews:

- a ghost producer containing the extracted term at the pointer;
- the fresh connection from that producer to the residual host; and
- placement validity in the host node's direct region.

The selected occurrence stays highlighted throughout the drag. The preview is green only when the candidate is kernel-valid and the pointer lies directly in the host node's region, outside the host body. A child/sibling region, outside-frame point, binder-invalid occurrence, or in-body release is red and cannot commit. Existing wires used by free ports may be emphasized, but their final relaxed routes are not fabricated in the preview.

Escape, mode changes, focus changes, proof motion, editor opening, and controller disposal clear hover and drag state.

## Commit policy and placement

The shared controller emits one request containing `{ node, path, at }`. Only the host commit policy differs:

- Edit calls the kernel fission applier, pushes the result through Edit history, identifies the new producer, and seeds it at `at`.
- Proof records `{ rule: 'fission', node, path }` through the active forward/backward proof commit path, identifies the kernel-minted producer after synchronous reconciliation, and seeds it at `at`.

Both modes use the kernel applier as semantic authority. Preview validation may apply the immutable kernel operation speculatively, but commit revalidates through the owning history path. No interaction code constructs or patches a diagram independently.

The gesture is implemented once. There is no proof menu row, Edit palette action, text path prompt, candidate-cycle mode, keyboard-only alternate, compatibility wrapper, or second mode-specific fission controller.

## Refusal behavior

Before outward movement, an invalid occurrence is communicated by its red internal highlight without producing repeated notices. On an attempted invalid release, the controller presents the kernel-compatible reason at the pointer:

- the selected subterm references a binder above it;
- the release is not outside the source node in its direct region; or
- the node/path ceased to exist while the gesture was active.

Every refusal leaves Edit/proof history and diagram identity unchanged. A successful commit clears selection consistently with other proof moves and clears every fission overlay.

## Validation

Path-geometry tests cover root, application function/argument, nested lambda body, leaves, repeated identical occurrences, bending, rotation, scaling, and final geometry after conversion motion. They prove hit traces coincide with painted primitives and deterministic overlap resolution returns the exact occurrence path.

Controller tests cover:

- Ctrl exclusion for hover and claim;
- Shift exclusion;
- connection priority at external wires and terminal halos;
- fission priority on internal occurrence traces;
- iteration retention elsewhere on selected nodes;
- still-click selection behavior;
- internal fission highlight versus enclosing iteration halo;
- valid, binder-invalid, wrong-region, in-body, and cancelled drags; and
- complete cleanup on lifecycle transitions.

Edit integration tests prove factorization, captured placement, undo/redo, free-wire preservation, and fusion round trip. Proof integration tests prove exact step recording, placement, undo/replay, and behavior in forward track, backward track, and both fixed fronts. Browser demonstrations exercise nested candidate selection, root extraction, fission/iteration disambiguation, Ctrl physics preservation, Edit history, and both Proof orientations.

Typecheck and every ordinary test must pass with zero failures. Physics implementation is unchanged; the separate opt-in physics suite is not run.
