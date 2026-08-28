# Orchard Browser Playtest Service Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Run the production Orchard frontend in a local browser against the existing Rust SQLite save authority, then directly playtest the resulting game.

**Architecture:** A loopback Axum service exposes the five existing `SaveStore` operations. The frontend constructs one `SaveClient` over an explicitly selected Tauri or HTTP transport; neither side implements save semantics or tries another transport after failure. A launcher supplies the service, origin, save directory, and per-run token to both processes.

**Tech Stack:** Rust 2021, Axum, Tokio, tower-http CORS, rusqlite, TypeScript, Vite, Vitest, shell launcher.

**Spec:** `docs/superpowers/specs/2026-08-28-orchard-browser-playtest-service-design.md`

## Global Constraints

- `SaveStore` remains the sole persistence authority.
- Browser and desktop transports are selected explicitly; no capability probing or fallback is allowed.
- The service binds only to `127.0.0.1`, accepts only the configured Vite origin, and requires a per-launch token.
- The service exposes no explicit save destination and no deletion operation.
- Browser playtesting uses ordinary SQLite saves in a git-ignored playtest directory.
- Browser playtesting does not add alternate controls: relative input activates
  free-flight controls, while world opening, rendering, and persistence remain
  independent of its availability.

---

### Task 1: Authenticated Rust playtest service

**Files:**
- Modify: `src-tauri/Cargo.toml`
- Modify: `src-tauri/src/lib.rs`
- Create: `src-tauri/src/playtest_server.rs`
- Create: `src-tauri/src/bin/orchard_playtest_server.rs`

**Interfaces:**
- Consumes: `SaveStore`, `CreateSlotInput`, `TreeUpdate`, and `CameraRecord` from `save_store`.
- Produces: `playtest_server::router(SaveStore, PlaytestServerConfig) -> axum::Router` and a binary configured by `ORCHARD_PLAYTEST_TOKEN`, `ORCHARD_PLAYTEST_ORIGIN`, `ORCHARD_PLAYTEST_SAVE_DIR`, and `ORCHARD_PLAYTEST_PORT`.

- [ ] **Step 1: Add failing route tests against a real temporary store**

Add tests in `playtest_server.rs` that construct the router with a temporary
`SaveStore`, send real HTTP requests through `tower::ServiceExt::oneshot`, and
assert:

```rust
#[tokio::test]
async fn authenticated_routes_create_list_load_and_update_an_ordinary_slot() {
    // POST create; POST list; POST load; POST update-tree; POST update-camera.
    // Re-open SaveStore on the same directory and assert the persisted values.
}

#[tokio::test]
async fn requests_without_the_exact_token_or_origin_never_touch_the_store() {
    // Missing/wrong token and wrong origin return 401/403; list remains empty.
}
```

The test payloads use literal camera and tree data. They assert returned JSON
and persisted store results, not handler call counts.

- [ ] **Step 2: Run RED**

Run:

```bash
cargo test --manifest-path src-tauri/Cargo.toml playtest_server
```

Expected: compilation fails because `playtest_server` and its router do not exist.

- [ ] **Step 3: Implement the minimal service**

Add optional runtime dependencies and a feature:

```toml
playtest-server = ["dep:axum", "dep:tokio", "dep:tower-http"]
axum = { version = "0.8", optional = true }
tokio = { version = "1", features = ["macros", "rt-multi-thread", "net"], optional = true }
tower-http = { version = "0.6", features = ["cors"], optional = true }
```

Define:

```rust
#[derive(Clone)]
pub struct PlaytestServerConfig {
    pub token: String,
    pub allowed_origin: HeaderValue,
}

pub fn router(store: SaveStore, config: PlaytestServerConfig) -> Router;
```

Routes are `POST /__orchard_playtest/save/list`, `/create`, `/load`,
`/update-tree`, and `/update-camera`, plus authenticated
`GET /__orchard_playtest/health`. Middleware rejects a missing or unequal
`x-orchard-playtest-token` before dispatch. CORS allows only the configured
origin, `POST`/`GET`, `content-type`, and `x-orchard-playtest-token`.

The binary parses the four required environment values, constructs
`SaveStore::new(save_dir)`, and binds `127.0.0.1:<port>`. Missing, malformed,
wildcard, or non-loopback configuration terminates with a concrete error.

- [ ] **Step 4: Run GREEN and Rust regression checks**

Run:

```bash
cargo test --manifest-path src-tauri/Cargo.toml playtest_server
cargo test --manifest-path src-tauri/Cargo.toml save_store
cargo check --manifest-path src-tauri/Cargo.toml --features playtest-server
```

Expected: all commands pass.

- [ ] **Step 5: Commit**

```bash
git add src-tauri/Cargo.toml src-tauri/Cargo.lock src-tauri/src/lib.rs src-tauri/src/playtest_server.rs src-tauri/src/bin/orchard_playtest_server.rs
git commit -m "feat(game): expose save store to browser playtests"
```

---

### Task 2: Explicit frontend transport and launcher

**Files:**
- Modify: `src/game/save-client.ts`
- Create: `tests/game/save-client.test.ts`
- Create: `scripts/playtest-game.sh`
- Modify: `package.json`
- Modify: `.gitignore`

**Interfaces:**
- Consumes: the five HTTP routes from Task 1.
- Produces: `createSaveClient(transport: SaveTransport): SaveClient`, `tauriSaveTransport`, `httpSaveTransport(config)`, and `npm run playtest:game`.

- [ ] **Step 1: Add failing transport-contract tests**

Create literal behavioral tests:

```ts
it('maps every SaveClient operation through one selected transport', async () => {
  // A recording transport returns literal wire responses.
  // Assert list/create/load/updateTree/updateCamera results and exact operations.
})

it('HTTP transport rejects a failed response without trying another transport', async () => {
  // One fetch returns status 500 with "save failed".
  // Assert the error and exactly one request.
})
```

The production mutation that makes these fail is direct use of Tauri `invoke`
inside `SaveClient` or any HTTP-to-Tauri retry.

- [ ] **Step 2: Run RED**

Run:

```bash
npx vitest run tests/game/save-client.test.ts
```

Expected: compilation fails because the transport constructors do not exist.

- [ ] **Step 3: Implement one decoding client over explicit transports**

Define:

```ts
export type SaveOperation = 'list' | 'create' | 'load' | 'update-tree' | 'update-camera'
export type SaveTransport = {
  request(operation: SaveOperation, input: Record<string, unknown>): Promise<unknown>
}

export function createSaveClient(transport: SaveTransport): SaveClient
export function httpSaveTransport(config: {
  baseUrl: string
  token: string
  fetch: typeof globalThis.fetch
}): SaveTransport
```

`createSaveClient` owns all existing decoders and maps the five public methods
to the five operations. `tauriSaveTransport` maps operation names to the
existing Tauri command names. `httpSaveTransport` sends one JSON POST with the
token header and throws the response text on non-2xx status.

Construct the exported `saveClient` from exactly one build value:

```ts
const transportName = import.meta.env.VITE_ORCHARD_SAVE_TRANSPORT ?? 'tauri'
```

Only `tauri` and `playtest-http` are accepted. The HTTP selection requires
`VITE_ORCHARD_PLAYTEST_URL` and `VITE_ORCHARD_PLAYTEST_TOKEN`; missing values
throw during startup. No catch block selects another transport.

- [ ] **Step 4: Add the process-owning launcher**

`scripts/playtest-game.sh` must:

1. Generate a UUID token with the bundled Node runtime.
2. Use `${ORCHARD_PLAYTEST_SAVE_DIR:-src-tauri/target/browser-playtest-saves}`.
3. Start `orchard_playtest_server` on port `1421`, origin
   `http://127.0.0.1:1420`, and the generated token.
4. Poll the authenticated health route until ready.
5. Start Vite on `127.0.0.1:1420` with the explicit HTTP transport values.
6. Trap exit and terminate only the service process it started.

Add `src-tauri/target/browser-playtest-saves/` to `.gitignore` and add:

```json
"playtest:game": "./scripts/playtest-game.sh"
```

- [ ] **Step 5: Run GREEN and integration checks**

Run:

```bash
npx vitest run tests/game/save-client.test.ts tests/game/model.test.ts tests/game/save-writer.test.ts
npm run typecheck
npm run build:game
```

Then start `npm run playtest:game` and use `curl` only to verify the authenticated
health boundary and one create/list/load cycle against the real service. The
browser remains the authority for UI validation in Task 3.

- [ ] **Step 6: Commit**

```bash
git add .gitignore package.json package-lock.json scripts/playtest-game.sh src/game/save-client.ts tests/game/save-client.test.ts
git commit -m "feat(game): run browser against production saves"
```

---

### Task 3: Direct browser playtest and repair loop

**Files:**
- Modify only files implicated by directly observed defects.
- Add a focused regression before each production repair.

**Interfaces:**
- Consumes: `npm run playtest:game` and the production game UI.
- Produces: directly exercised browser evidence for the complete primary flow.

- [ ] **Step 1: Start and inspect the real browser flow**

Run `npm run playtest:game`, reload the existing local browser tab, and directly:

1. Confirm the menu lists saves without an IPC error.
2. Create `Browser Playtest` and inspect all resulting UI and mode state.
3. Use free-flight movement and look.
4. Use the tool and verify the tree changes while camera mode and pose remain stable.
5. Enter orbit with the primary button, inspect pointing, and use the tool.
6. Leave orbit, reload the page, and load the same slot.
7. Confirm both tree and camera persistence.

- [ ] **Step 2: Repair each directly observed repository defect**

For every defect, trace its root cause, add a focused failing behavioral test,
run RED, implement the smallest complete repair, run GREEN, commit, reload, and
repeat the exact direct interaction. Do not introduce an alternate camera/input
path to accommodate the browser-control surface; unavailable relative input keeps
the opened world available with its ordinary resume cue.

- [ ] **Step 3: Run final automated validation**

Run:

```bash
npm run typecheck
npm test
cargo test --manifest-path src-tauri/Cargo.toml
cargo check --manifest-path src-tauri/Cargo.toml --features playtest-server
git diff --check
```

- [ ] **Step 4: Commit any playtest-owned repairs**

Commit each coherent tested repair separately. Finish with a clean worktree.
