# Electron App Launch Design

## Outcome

`npm run app` is the one authoritative way to launch the playable desktop game. Vite remains responsible for compiling the renderer, while Electron remains responsible for the window, preload bridge, persistence, fullscreen, and exit lifecycle. A renderer served directly by Vite is not presented as a playable application.

## Startup ownership

The `app` package script runs the existing deterministic desktop build and starts Electron only after both renderer and Electron outputs succeed. The competing `desktop:dev` launcher is removed. Renderer compilation continues to use `vite build app`; Linux packaging continues to consume the same built outputs.

The resulting flow is:

1. Vite builds `app/` into `app/dist/`.
2. TypeScript builds Electron main/preload code into `dist-electron/`.
3. Electron creates the secure window and installs the isolated preload.
4. The renderer obtains `window.cursebreakerPlatform`, restores state, and mounts the archive or active puzzle.

## Failure behavior

The renderer bootstrap owns a final rejection boundary. If platform acquisition, save loading, or initial mounting fails, it logs the original exception and replaces the empty host with a small accessible launch-failure message. This is diagnostic fallback only; it does not emulate the preload or create a browser/local-storage runtime.

## Validation

- A package-contract test first fails against `app: vite app`, then requires `app` to build the desktop outputs and launch Electron while rejecting `desktop:dev` and a standalone Vite app command.
- A built-renderer browser regression forces initial save loading to fail and proves the launch-failure boundary is visible rather than black.
- Existing platform, authoritative runtime, CSP, typecheck, and desktop-build validation remain green.
- A realistic Linux check launches the exact `npm run app` command, captures renderer errors, confirms visible archive records, activates the first unlocked artifact, and confirms puzzle/proof/timeline rendering through the real preload and IPC path.

The proof-physics battery remains disabled and unrun because startup ownership does not alter proof mechanics.
