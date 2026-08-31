# Repository Agent Instructions

## Provisional implementation

Treat new implementation work as a provisional spike until the requested behavior works and the changed dependency path has then been reviewed with the `simplify-code-tarpit` skill and any other standards genuinely implicated by the change. If that review finds poor architecture or unjustified accidental complexity, backtrack to the design decision that introduced it and redo all dependent work using what the spike revealed; preserve only work independent of that decision. Keep the implementation only after it passes this review. Passing tests alone does not make a spike permanent.

## Live developer content

Treat live developer content edits as direct changes to the current content authority and let existing runtime consumers observe them immediately. Add protective machinery only for a concrete gameplay failure, crash, logically invalid state, or destructive content loss required by the requested behavior. A previously observed value changing is not harm by itself and does not justify snapshots, versions, migrations, synchronization, transactional isolation, or compatibility behavior.

## Direct in-app validation

A user-facing feature is not complete until the agent has directly exercised it in the running application through the same user interface and controls available to a person using the product.

Direct exercise means performing the real interaction through the app or browser interaction surface. Test runners, scripted input, injected events, page evaluation, screenshots, logs, builds, and smoke checks are additional evidence, not substitutes; they may produce a different event sequence from real interaction.

Before finalization, use the primary changed flow and relevant adjacent transitions as a user would. After each interaction, inspect the complete resulting UI state, including unintended mode, focus, navigation, selection, and presentation changes—not only the intended data mutation or success signal. Repair every issue found and repeat the direct interaction.

If direct interaction is impossible in the available environment, do not substitute automation and do not claim the feature is complete. State the exact blocker and the strongest supplemental validation performed.
