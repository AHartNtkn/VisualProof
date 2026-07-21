# Head-strip interaction design

## Outcome

Players can author `headStrip` directly on the diagram by dragging from one term output leg to another term output leg on the same binary equality wire. The interaction uses the established green connection preview, identifies the two endpoints, destructively replaces their equation with corresponding argument equations, and never requires the proof menu.

## Interaction grammar

- A still primary press remains an ordinary selection click.
- Dragging a rendered wire to a different wire remains the connection/join interaction.
- Dragging from a term output endpoint leg to a distinct term output endpoint leg on the same binary wire applies `headStrip` to those two nodes.
- A same-wire release on a trunk, junction, source endpoint, or non-output endpoint does not guess a pair and refuses with a specific message.
- A transverse secondary-button slash remains the only construction sever gesture. Double-click severing and its mode toggle are removed.
- Proof-mode double-click fusion is unchanged.

With three or more endpoints on one equality wire, endpoint hit testing still identifies the attempted pair, but the kernel refuses `headStrip` and requires the wire to be severed first.

## Ownership and dispatch

One shared connection-drag unit owns source capture, target hit testing, movement threshold behavior, and the green overlay. Its hit result carries the wire and, only when the rendered leg terminates at a node port, the concrete diagram endpoint.

Edit mode supplies a commit policy that joins different source and target wires. Proof mode supplies a commit policy that:

1. emits `headStrip` for distinct term-output endpoints on the same binary wire and surfaces the kernel's sever-first refusal for a multi-endpoint wire;
2. resolves a different-wire connection to the first kernel-valid member of the already-approved join family (`wireJoin`, `congruenceJoin`, or equal-anchor contraction), recording that proof step while keeping the resolution invisible because all successful candidates have the same visible merged-wire result; and
3. refuses unsupported or ambiguous releases without inventing an endpoint.

Certificate-bearing candidates use the existing fueled conversion search, and every candidate is dry-run through its real applier before commit. Candidate order is deterministic but is not user-facing proof semantics.

The kernel applier remains the sole legality authority at commit. Preview discovery may suppress obviously invalid targets, but it does not replace kernel validation.

## Feedback

During a drag, the pointer segment uses the existing valid green. A valid target leg is emphasized in green. Invalid same-wire releases explain that the gesture must end on another term's output strand. Kernel refusals are surfaced verbatim when a geometrically identified pair fails the semantic gates, including the requirement to sever extra endpoints before head stripping.

## Validation

Focused tests cover endpoint-leg resolution, trunk non-resolution, Edit-mode different-wire joining through the shared unit, Proof-mode resolution of each join-family member, destructive two-node head stripping, sever-first refusal on a three-output wire, invalid same-wire releases, selection preservation, and removal of every double-click sever path and control. Type checking and the ordinary non-physics suite provide regression coverage; physics tests remain opt-in because physics behavior is unchanged.
