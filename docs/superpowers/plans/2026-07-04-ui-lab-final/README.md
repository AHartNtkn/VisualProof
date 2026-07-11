# Final interaction-design evidence

This directory is an inert record of the visual proof assistant redesign. It is
not an application, alternate mode, test authority, or supported runtime entry
point. Production behavior lives under `src/`; production browser checks live
under `e2e/`.

## Authorities

- [`../2026-07-03-plan-19-interface-overhaul.md`](../2026-07-03-plan-19-interface-overhaul.md)
  records the round-by-round user verdicts and the 26 interaction laws.
- [`../2026-07-04-plan-20-interaction-integration.md`](../2026-07-04-plan-20-interaction-integration.md)
  records production integration and final teardown.
- [`ui-lab/index.html`](ui-lab/index.html) is the historical visual index.

## Preserved evidence

- `ui-lab/` is the complete former demo tree, including the converged
  `shared.ts`, `composite.ts`, `verdict.ts`, `session5.ts`, `chrome.ts`,
  `spawn.ts`, `history.ts`, and `round7.ts` mechanics as well as the later
  approved layout, aesthetic, library, feedback, and comprehension rounds.
- `verification/` contains the former demo-only Playwright checks. They are
  retained to explain what the demonstrations exercised, but Playwright no
  longer discovers or runs them.
- `production-prototypes/` contains displaced executable prototypes whose
  responsibilities now belong to production systems. Nothing in source or
  tests imports them.

Relative imports and URLs inside preserved files intentionally retain their
historical spelling. They are provenance, not supported execution instructions.
