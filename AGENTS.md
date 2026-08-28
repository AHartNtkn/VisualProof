# Repository Agent Instructions

## Direct in-app validation

A user-facing feature is not complete until the agent has directly exercised it in the running application through the same user interface and controls available to a person using the product.

Direct exercise means performing the real interaction through the app or browser interaction surface. Test runners, scripted input, injected events, page evaluation, screenshots, logs, builds, and smoke checks are additional evidence, not substitutes; they may produce a different event sequence from real interaction.

Before finalization, use the primary changed flow and relevant adjacent transitions as a user would. After each interaction, inspect the complete resulting UI state, including unintended mode, focus, navigation, selection, and presentation changes—not only the intended data mutation or success signal. Repair every issue found and repeat the direct interaction.

If direct interaction is impossible in the available environment, do not substitute automation and do not claim the feature is complete. State the exact blocker and the strongest supplemental validation performed.
