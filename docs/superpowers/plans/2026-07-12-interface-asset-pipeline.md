# Cursebreaker Central Lens and Asset Pipeline Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the verified production-art pipeline and replace the game branch's proof-assistant browser entry with a real one-puzzle Cursebreaker shell displaying the opening artifact through an authored central lens and compact timeline lever.

**Architecture:** Blender and GIMP sources own art, a manifest owns production inventory and provenance, and deterministic scripts own derived exports. The first runtime slice reuses `ProofFrontViewport` as the already validated backward interaction surface, wraps it in a game-owned session controller and pointer-transparent lens composition, and replaces the assistant app entry rather than styling or retaining a second product UI. The milestone stops at realistic desktop and compact review renders; the surrounding desk cannot begin until the lens family is approved.

**Tech Stack:** TypeScript 5.5, Vite 5, Vitest 2, Playwright 1.60, Canvas 2D, CSS nine-slice composition, Bash, Blender 4.5.11 LTS Python API, transparent PNG.

## Global Constraints

- The game branch contains one browser product: Cursebreaker. `app/main.ts` must no longer mount the proof-assistant shell.
- The live Canvas 2D proof renderer remains the sole proof-surface authority.
- Reuse the existing backward `ProofFrontViewport`; do not fork proof gestures or alter proof interactions.
- The lens is a straight-on, nearly viewport-height rounded square.
- No menu, title bar, orbiting control, unexplained indicator, or legend may be added to the lens.
- The timeline lever is centered beneath the glass and no wider than 40% of the lens.
- Decorative layers use `pointer-events: none`, have no focus, and are absent from the accessibility tree.
- Use the existing `DARK` theme (`Dark (Slate)`) for the proof diagram.
- Generated concept images and SVG/CSS layout mockups are reference material only, never production sources.
- Blender is exactly 4.5.11 LTS for Linux x64. The archive SHA-256 is `05ed7bd41bf3e61ae4f4a7cdc364c43088bf8b3fed702c2269c018fdf63a2188`.
- The first family contains only frame, glass, frame shadow, lever housing, and lever handle.
- The first review master is 4096×4096 for square layers; runtime reduction happens only after visual review and browser profiling.
- The first family uses authored procedural brass and glass and has no external texture dependency.
- Runtime assets are transparent PNG and are never edited directly.
- Physics behavior, physics files, and `npm run test:physics` are outside scope.
- A family remains `candidate` until the user approves realistic desktop and compact application renders.

---

## File and responsibility map

### Toolchain and asset authority

- Modify `.gitignore` — ignore `.tools/` and render staging without ignoring committed generated assets.
- Create `scripts/assets/install-blender.sh` — provision and verify the pinned portable Blender binary.
- Create `scripts/assets/check-blender.sh` — fail unless the pinned binary reports 4.5.11.
- Create `scripts/assets/render-interface.sh` — validate, render one declared family to staging, and validate outputs.
- Create `scripts/assets/blender/render_family.py` — Blender-only deterministic scene/render configuration.
- Create `scripts/assets/promote-interface.ts` — atomically promote staged candidate files and update manifest hashes.
- Create `scripts/assets/manifest.ts` — manifest types, parsing, invariant checks, hashing, and file validation.
- Create `scripts/assets/validate-interface-assets.ts` — repository validation CLI.
- Create `assets/interface/manifest.json` with the first rendered family — single asset/provenance/review inventory; no invalid empty production manifest is committed beforehand.
- Create `assets/interface/source/blender/central-lens.blend` — editable mechanical authority.
- Create `assets/interface/source/gimp/.gitkeep` — declared future organic-source location; no `.xcf` is invented for this family.
- Create `assets/interface/source/inputs/README.md` — external-input admission and provenance rule.
- Create `assets/interface/generated/central-lens/*.png` — committed candidate exports.

### Game runtime

- Create `src/game/interface/lens-layout.ts` — pure viewport-to-square-lens geometry.
- Create `src/game/interface/timeline-lever.ts` — game presentation of the existing timeline cursor, using the shared cursor mapping.
- Create `src/game/interface/mount.ts` — game session, backward viewport, resize/frame loop, completion, timeline, and debug seam.
- Create `src/game/interface/index.ts` — public interface barrel.
- Modify `src/game/index.ts` — export the browser game interface.
- Replace `app/main.ts` — mount Cursebreaker only.
- Replace `app/index.html` — Cursebreaker document and one mount root.
- Replace `app/style.css` — dark desk ground, square lens composition, pointer-transparent assets, and compact lever.

### Validation

- Create `tests/scripts/blender-toolchain.test.ts` — pin and shell syntax tests.
- Create `tests/assets/manifest.test.ts` — manifest invariant and file-validation tests.
- Create `tests/game/lens-layout.test.ts` — square, height-first, compact geometry tests.
- Create `tests/game/timeline-lever.test.ts` — shared cursor mapping and handle-position tests.
- Replace assistant-product E2E files under `e2e/` with `e2e/cursebreaker.spec.ts` — one-product boot, real opening artifact, backward completion, lever semantics, asset loading, and interaction-boundary checks.
- Create `scripts/assets/capture-central-lens.mjs` — deterministic desktop and compact review captures from the real built app.

---

### Task 1: Pinned Blender provisioning

**Files:**
- Modify: `.gitignore`
- Create: `scripts/assets/install-blender.sh`
- Create: `scripts/assets/check-blender.sh`
- Create: `tests/scripts/blender-toolchain.test.ts`

**Interfaces:**
- Consumes: Linux x64, `curl`, `sha256sum`, `tar`, and the pinned archive hash in Global Constraints.
- Produces: executable `.tools/blender/4.5.11/blender`; `scripts/assets/check-blender.sh` exits zero only for Blender 4.5.11.

- [ ] **Step 1: Write the failing toolchain contract test**

```ts
// tests/scripts/blender-toolchain.test.ts
import { readFileSync } from 'node:fs'
import { spawnSync } from 'node:child_process'
import { describe, expect, it } from 'vitest'

const install = 'scripts/assets/install-blender.sh'
const check = 'scripts/assets/check-blender.sh'

describe('interface asset Blender toolchain', () => {
  it('pins the exact LTS archive and refuses an unverified download', () => {
    const source = readFileSync(install, 'utf8')
    expect(source).toContain("VERSION='4.5.11'")
    expect(source).toContain("ARCHIVE='blender-4.5.11-linux-x64.tar.xz'")
    expect(source).toContain("SHA256='05ed7bd41bf3e61ae4f4a7cdc364c43088bf8b3fed702c2269c018fdf63a2188'")
    expect(source).toContain('sha256sum --check --status')
    expect(source).not.toContain('curl -k')
  })

  it.each([install, check])('%s has valid Bash syntax', (path) => {
    expect(spawnSync('bash', ['-n', path], { encoding: 'utf8' })).toMatchObject({ status: 0, stderr: '' })
  })
})
```

- [ ] **Step 2: Run the test and verify the scripts are missing**

Run: `npx vitest run tests/scripts/blender-toolchain.test.ts`

Expected: FAIL with `ENOENT: no such file or directory, open 'scripts/assets/install-blender.sh'`.

- [ ] **Step 3: Implement fail-closed installation and version checking**

```bash
#!/usr/bin/env bash
# scripts/assets/install-blender.sh
set -euo pipefail

VERSION='4.5.11'
ARCHIVE='blender-4.5.11-linux-x64.tar.xz'
SHA256='05ed7bd41bf3e61ae4f4a7cdc364c43088bf8b3fed702c2269c018fdf63a2188'
BASE_URL='https://mirror.clarkson.edu/blender/release/Blender4.5'
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
DEST="$ROOT/.tools/blender/$VERSION"
CACHE="$ROOT/.tools/cache/$ARCHIVE"
STAGING="$ROOT/.tools/blender/.4.5.11-staging"

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo 'Blender provisioning requires Linux x86_64.' >&2
  exit 1
fi
mkdir -p "$(dirname "$CACHE")" "$(dirname "$DEST")"
if [[ ! -f "$CACHE" ]]; then
  curl --fail --location --proto '=https' --tlsv1.2 \
    --output "$CACHE.part" "$BASE_URL/$ARCHIVE"
  mv "$CACHE.part" "$CACHE"
fi
if ! printf '%s  %s\n' "$SHA256" "$CACHE" | sha256sum --check --status; then
  echo "Checksum verification failed for $ARCHIVE." >&2
  exit 1
fi
rm -rf "$STAGING"
mkdir -p "$STAGING"
tar -xJf "$CACHE" --strip-components=1 -C "$STAGING"
"$STAGING/blender" --version | head -n 1 | grep -Fx 'Blender 4.5.11'
rm -rf "$DEST"
mv "$STAGING" "$DEST"
printf '%s  %s\n' "$SHA256" "$ARCHIVE" > "$DEST/ARCHIVE.sha256"
echo "Installed Blender 4.5.11 at $DEST/blender"
```

```bash
#!/usr/bin/env bash
# scripts/assets/check-blender.sh
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
BIN="$ROOT/.tools/blender/4.5.11/blender"
[[ -x "$BIN" ]] || { echo 'Blender 4.5.11 is not installed; run scripts/assets/install-blender.sh.' >&2; exit 1; }
[[ "$($BIN --version | head -n 1)" == 'Blender 4.5.11' ]] || { echo 'Installed Blender is not 4.5.11.' >&2; exit 1; }
printf '%s\n' "$BIN"
```

Add to `.gitignore`:

```gitignore
.tools/
assets/interface/.staging/
```

Make the scripts executable with `chmod +x scripts/assets/install-blender.sh scripts/assets/check-blender.sh`.

- [ ] **Step 4: Run the focused test**

Run: `npx vitest run tests/scripts/blender-toolchain.test.ts`

Expected: 3 tests PASS.

- [ ] **Step 5: Provision and validate the real tool**

Run: `scripts/assets/install-blender.sh`

Expected: the archive verifies, extraction completes, and the last line is `Installed Blender 4.5.11 at .../.tools/blender/4.5.11/blender`.

Run: `scripts/assets/check-blender.sh`

Expected: one absolute path ending in `.tools/blender/4.5.11/blender`.

- [ ] **Step 6: Commit the provisioning boundary**

```bash
git add .gitignore scripts/assets/install-blender.sh scripts/assets/check-blender.sh tests/scripts/blender-toolchain.test.ts
git commit -m "build(game): pin interface Blender toolchain"
```

---

### Task 2: Manifest authority and validation

**Files:**
- Create: `assets/interface/source/gimp/.gitkeep`
- Create: `assets/interface/source/inputs/README.md`
- Create: `scripts/assets/manifest.ts`
- Create: `scripts/assets/validate-interface-assets.ts`
- Create: `tests/assets/manifest.test.ts`
- Modify: `package.json`

**Interfaces:**
- Consumes: repository-relative paths and Node's SHA-256 implementation.
- Produces: `parseInterfaceManifest(value: unknown): InterfaceAssetManifest`; `validateInterfaceAssets(root: string, manifest: InterfaceAssetManifest, checkOutputs?: boolean): string[]`; CLI `npm run assets:validate`.

- [ ] **Step 1: Write failing manifest tests**

```ts
// tests/assets/manifest.test.ts
import { mkdtempSync, mkdirSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import { parseInterfaceManifest, validateInterfaceAssets } from '../../scripts/assets/manifest'

const candidate = {
  format: 'cursebreaker-interface-assets', version: 1,
  toolchain: { blender: '4.5.11' },
  families: [{
    id: 'central-lens', source: 'assets/interface/source/blender/central-lens.blend',
    sourceSha256: 'a'.repeat(64), tool: 'blender', toolVersion: '4.5.11',
    renderScript: 'scripts/assets/blender/render_family.py', externalInputs: [],
    review: 'candidate',
    outputs: [{ id: 'frame', path: 'assets/interface/generated/central-lens/frame.png',
      scene: 'Lens_Frame', width: 4096, height: 4096, colorSpace: 'sRGB', alpha: 'straight',
      slice: { top: 560, right: 560, bottom: 560, left: 560 }, sha256: 'b'.repeat(64) }],
  }],
}

describe('interface asset manifest', () => {
  it('accepts the exact candidate contract', () => {
    expect(parseInterfaceManifest(candidate).families[0]?.id).toBe('central-lens')
  })

  it('rejects path escapes and invalid stretch insets', () => {
    expect(() => parseInterfaceManifest({ ...candidate, families: [{ ...candidate.families[0], source: '../lens.blend' }] })).toThrow(/repository-relative/)
    expect(() => parseInterfaceManifest({ ...candidate, families: [{ ...candidate.families[0], outputs: [{ ...candidate.families[0].outputs[0], slice: { top: 3000, right: 560, bottom: 3000, left: 560 } }] }] })).toThrow(/slice/)
  })

  it('reports missing and hash-mismatched declared files', () => {
    const root = mkdtempSync(join(tmpdir(), 'cursebreaker-assets-'))
    mkdirSync(join(root, 'assets/interface/source/blender'), { recursive: true })
    mkdirSync(join(root, 'assets/interface/generated/central-lens'), { recursive: true })
    writeFileSync(join(root, candidate.families[0].source), 'source')
    writeFileSync(join(root, candidate.families[0].outputs[0].path), 'output')
    expect(validateInterfaceAssets(root, parseInterfaceManifest(candidate), true)).toEqual(expect.arrayContaining([
      expect.stringMatching(/source SHA-256/), expect.stringMatching(/output SHA-256/),
    ]))
  })
})
```

- [ ] **Step 2: Run the tests and verify the module is missing**

Run: `npx vitest run tests/assets/manifest.test.ts`

Expected: FAIL because `scripts/assets/manifest.ts` does not exist.

- [ ] **Step 3: Implement the manifest parser and validator**

Create `scripts/assets/manifest.ts` with these public types and functions:

```ts
import { existsSync, readFileSync } from 'node:fs'
import { createHash } from 'node:crypto'
import { resolve, sep } from 'node:path'

export type AssetSlice = { readonly top: number; readonly right: number; readonly bottom: number; readonly left: number }
export type AssetOutput = {
  readonly id: string; readonly path: string; readonly scene: string
  readonly width: number; readonly height: number
  readonly colorSpace: 'sRGB'; readonly alpha: 'straight'
  readonly slice?: AssetSlice; readonly sha256: string
}
export type AssetFamily = {
  readonly id: string; readonly source: string; readonly sourceSha256: string
  readonly tool: 'blender' | 'gimp'; readonly toolVersion: string
  readonly renderScript: string; readonly externalInputs: readonly {
    readonly id: string; readonly path: string; readonly url: string
    readonly license: 'CC0-1.0'; readonly sha256: string
  }[]
  readonly review: 'candidate' | 'approved'; readonly outputs: readonly AssetOutput[]
}
export type InterfaceAssetManifest = {
  readonly format: 'cursebreaker-interface-assets'; readonly version: 1
  readonly toolchain: { readonly blender: '4.5.11' }
  readonly families: readonly AssetFamily[]
}

const object = (value: unknown, label: string): Record<string, unknown> => {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) throw new Error(`${label} must be an object`)
  return value as Record<string, unknown>
}
const text = (value: unknown, label: string): string => {
  if (typeof value !== 'string' || value.trim() !== value || value === '') throw new Error(`${label} must be a trimmed nonempty string`)
  return value
}
const integer = (value: unknown, label: string): number => {
  if (!Number.isSafeInteger(value) || (value as number) <= 0) throw new Error(`${label} must be a positive safe integer`)
  return value as number
}
const digest = (value: unknown, label: string): string => {
  const result = text(value, label)
  if (!/^[0-9a-f]{64}$/.test(result)) throw new Error(`${label} must be a lowercase SHA-256`)
  return result
}
const path = (value: unknown, label: string): string => {
  const result = text(value, label)
  if (result.startsWith('/') || result.split('/').includes('..')) throw new Error(`${label} must be repository-relative without traversal`)
  return result
}

export function parseInterfaceManifest(value: unknown): InterfaceAssetManifest {
  const root = object(value, 'manifest')
  if (root.format !== 'cursebreaker-interface-assets' || root.version !== 1) throw new Error('unsupported interface asset manifest')
  const toolchain = object(root.toolchain, 'manifest.toolchain')
  if (toolchain.blender !== '4.5.11') throw new Error('manifest.toolchain.blender must be 4.5.11')
  if (!Array.isArray(root.families)) throw new Error('manifest.families must be an array')
  const ids = new Set<string>()
  const families = root.families.map((raw, familyIndex): AssetFamily => {
    const family = object(raw, `family[${familyIndex}]`)
    const id = text(family.id, `family[${familyIndex}].id`)
    if (ids.has(id)) throw new Error(`duplicate family '${id}'`)
    ids.add(id)
    if (family.tool !== 'blender' && family.tool !== 'gimp') throw new Error(`family '${id}' has invalid tool`)
    if (family.review !== 'candidate' && family.review !== 'approved') throw new Error(`family '${id}' has invalid review state`)
    if (!Array.isArray(family.externalInputs) || !Array.isArray(family.outputs)) throw new Error(`family '${id}' inputs and outputs must be arrays`)
    const outputIds = new Set<string>()
    const outputs = family.outputs.map((rawOutput, outputIndex): AssetOutput => {
      const output = object(rawOutput, `family '${id}' output[${outputIndex}]`)
      const outputId = text(output.id, `family '${id}' output id`)
      if (outputIds.has(outputId)) throw new Error(`family '${id}' has duplicate output '${outputId}'`)
      outputIds.add(outputId)
      const width = integer(output.width, `output '${outputId}' width`)
      const height = integer(output.height, `output '${outputId}' height`)
      let slice: AssetSlice | undefined
      if (output.slice !== undefined) {
        const rawSlice = object(output.slice, `output '${outputId}' slice`)
        slice = { top: integer(rawSlice.top, 'slice.top'), right: integer(rawSlice.right, 'slice.right'), bottom: integer(rawSlice.bottom, 'slice.bottom'), left: integer(rawSlice.left, 'slice.left') }
        if (slice.top + slice.bottom >= height || slice.left + slice.right >= width) throw new Error(`output '${outputId}' slice leaves no stretchable center`)
      }
      if (output.colorSpace !== 'sRGB' || output.alpha !== 'straight') throw new Error(`output '${outputId}' must use sRGB straight alpha`)
      return { id: outputId, path: path(output.path, `output '${outputId}' path`), scene: text(output.scene, `output '${outputId}' scene`), width, height, colorSpace: 'sRGB', alpha: 'straight', ...(slice === undefined ? {} : { slice }), sha256: digest(output.sha256, `output '${outputId}' sha256`) }
    })
    return {
      id, source: path(family.source, `family '${id}' source`), sourceSha256: digest(family.sourceSha256, `family '${id}' sourceSha256`),
      tool: family.tool, toolVersion: text(family.toolVersion, `family '${id}' toolVersion`), renderScript: path(family.renderScript, `family '${id}' renderScript`),
      externalInputs: family.externalInputs.map((entry, index) => {
        const input = object(entry, `family '${id}' input[${index}]`)
        if (input.license !== 'CC0-1.0') throw new Error(`family '${id}' input license must be CC0-1.0`)
        return { id: text(input.id, 'input.id'), path: path(input.path, 'input.path'), url: text(input.url, 'input.url'), license: 'CC0-1.0', sha256: digest(input.sha256, 'input.sha256') }
      }),
      review: family.review, outputs,
    }
  })
  return { format: 'cursebreaker-interface-assets', version: 1, toolchain: { blender: '4.5.11' }, families }
}

export const sha256File = (file: string): string => createHash('sha256').update(readFileSync(file)).digest('hex')

export function validateInterfaceAssets(root: string, manifest: InterfaceAssetManifest, checkOutputs = true): string[] {
  const errors: string[] = []
  const inside = (relative: string): string => {
    const absolute = resolve(root, relative)
    if (absolute !== root && !absolute.startsWith(`${resolve(root)}${sep}`)) throw new Error(`path escapes repository: ${relative}`)
    return absolute
  }
  for (const family of manifest.families) {
    const source = inside(family.source)
    if (!existsSync(source)) errors.push(`missing source: ${family.source}`)
    else if (sha256File(source) !== family.sourceSha256) errors.push(`source SHA-256 mismatch: ${family.source}`)
    for (const input of family.externalInputs) {
      const file = inside(input.path)
      if (!existsSync(file)) errors.push(`missing external input: ${input.path}`)
      else if (sha256File(file) !== input.sha256) errors.push(`external input SHA-256 mismatch: ${input.path}`)
    }
    if (!checkOutputs) continue
    for (const output of family.outputs) {
      const file = inside(output.path)
      if (!existsSync(file)) errors.push(`missing output: ${output.path}`)
      else if (sha256File(file) !== output.sha256) errors.push(`output SHA-256 mismatch: ${output.path}`)
    }
  }
  return errors
}
```

Create `scripts/assets/validate-interface-assets.ts` as a thin CLI that reads `assets/interface/manifest.json`, calls both functions with `process.cwd()`, prints each error to stderr, and exits 1 when the error list is nonempty.

- [ ] **Step 4: Add the provenance boundary and manifest command**

Do not create `assets/interface/manifest.json` yet: a production manifest naming missing sources or fake checksums would be an invalid parallel account of the repository. Task 3 creates it atomically when the first staged render is promoted. The promoter owns this exact five-output table and computes hashes from the actual files:

```ts
const outputSpecs = [
  { id: 'frame', file: 'frame.png', scene: 'Lens_Frame', width: 4096, height: 4096,
    slice: { top: 560, right: 560, bottom: 560, left: 560 } },
  { id: 'glass', file: 'glass.png', scene: 'Lens_Glass', width: 4096, height: 4096 },
  { id: 'shadow', file: 'shadow.png', scene: 'Lens_Shadow', width: 4096, height: 4096 },
  { id: 'lever-housing', file: 'lever-housing.png', scene: 'Lever_Housing', width: 2048, height: 512 },
  { id: 'lever-handle', file: 'lever-handle.png', scene: 'Lever_Handle', width: 512, height: 512 },
] as const

const source = 'assets/interface/source/blender/central-lens.blend'
const manifest: InterfaceAssetManifest = {
  format: 'cursebreaker-interface-assets', version: 1,
  toolchain: { blender: '4.5.11' },
  families: [{
    id: 'central-lens', source, sourceSha256: sha256File(resolve(root, source)),
    tool: 'blender', toolVersion: '4.5.11',
    renderScript: 'scripts/assets/blender/render_family.py', externalInputs: [], review: 'candidate',
    outputs: outputSpecs.map((spec) => {
      const path = `assets/interface/generated/central-lens/${spec.file}`
      return { id: spec.id, path, scene: spec.scene, width: spec.width, height: spec.height,
        colorSpace: 'sRGB', alpha: 'straight', ...('slice' in spec ? { slice: spec.slice } : {}),
        sha256: sha256File(resolve(root, path)) }
    }),
  }],
}
```

`assets/interface/source/inputs/README.md` must state: only inputs named in the manifest may be committed; each requires its original URL, `CC0-1.0`, and exact checksum; generated concept images are forbidden. Add `"assets:validate": "tsx scripts/assets/validate-interface-assets.ts"` to `package.json`.

- [ ] **Step 5: Run focused tests**

Run: `npx vitest run tests/assets/manifest.test.ts`

Expected: 3 tests PASS.

- [ ] **Step 6: Commit manifest authority**

```bash
git add package.json assets/interface/source/gimp/.gitkeep assets/interface/source/inputs/README.md scripts/assets/manifest.ts scripts/assets/validate-interface-assets.ts tests/assets/manifest.test.ts
git commit -m "build(game): add interface asset manifest authority"
```

---

### Task 3: Authored central-lens source and deterministic exports

**Files:**
- Create: `assets/interface/source/blender/central-lens.blend`
- Create: `scripts/assets/blender/render_family.py`
- Create: `scripts/assets/render-interface.sh`
- Create: `scripts/assets/promote-interface.ts`
- Create: `assets/interface/generated/central-lens/frame.png`
- Create: `assets/interface/generated/central-lens/glass.png`
- Create: `assets/interface/generated/central-lens/shadow.png`
- Create: `assets/interface/generated/central-lens/lever-housing.png`
- Create: `assets/interface/generated/central-lens/lever-handle.png`
- Modify: `assets/interface/manifest.json`
- Create: `tests/assets/render-contract.test.ts`

**Interfaces:**
- Consumes: Blender binary from Task 1 and manifest from Task 2.
- Produces: editable `.blend` with scenes `Lens_Frame`, `Lens_Glass`, `Lens_Shadow`, `Lever_Housing`, and `Lever_Handle`; staged and promoted PNGs matching the manifest.

- [ ] **Step 1: Write the failing render-contract test**

The test must assert that every manifest output has a unique scene and path, the family has no external input, frame slice is exactly 560 pixels on every edge, Blender source/output files exist, PNG dimensions match the manifest, and `npm run assets:validate` exits zero. Parse PNG dimensions from the eight-byte PNG signature plus IHDR width/height; do not add an image dependency.

Run: `npx vitest run tests/assets/render-contract.test.ts`

Expected: FAIL because the Blender source and generated PNGs do not exist.

- [ ] **Step 2: Author the editable Blender source**

Open `.tools/blender/4.5.11/blender` and save the source as `assets/interface/source/blender/central-lens.blend`. A temporary scratch Python authoring script may be used to establish geometry, but it must live outside the repository and be deleted after the `.blend` is inspected and saved; the `.blend` is the committed editable authority.

The source must use real geometry, bevels, materials, and lighting—not a traced image or a flat colored rectangle—and contain this exact object/material organization:

| Scene | Required authored contents |
|---|---|
| `Lens_Frame` | Orthographic camera at `(0, 0, 20)`, 10×10 square framing; rounded-square outer brass rail; recessed inner brass lip; four distinct corner escutcheons; eight small fasteners; slight non-symmetric wear masks; transparent center. The unornamented edge run between 560-pixel slice boundaries must have no unique feature. |
| `Lens_Glass` | Same camera; thin rounded-square glass plane inside the inner lip; edge darkening and two broad, low-opacity reflections confined away from the central proof focus; transparent background. |
| `Lens_Shadow` | Same camera; frame-only soft shadow/ambient occlusion with no desk color baked into it. |
| `Lever_Housing` | Orthographic 4:1 camera; compact recessed brass track, 11 physical notches, two end stops, and a darker mounting plate; transparent background. |
| `Lever_Handle` | Square orthographic camera; separate short lever carriage and narrow grip centered at origin; no track or notches; transparent background. |

Use three named procedural materials: `Aged Brass` (`#6f5427` base, metallic 0.86, roughness varying 0.25–0.52 through Noise→ColorRamp), `Dark Recess` (`#15171b`, metallic 0.55, roughness 0.48), and `Lens Glass` (near-black blue-green tint, transmission 0.18, roughness 0.16, alpha below 0.12). Edge wear is restrained: bevel-edge brightening and localized dark oxidation, not uniform grunge. Use a large warm key area light from upper left, a weaker cool fill from lower right, and a narrow warm rim; keep the camera axis straight.

Render one 1024-pixel contact sheet during authoring and inspect it before accepting the `.blend`. Reject and revise the source if the frame reads as a flat UI border, if the center is materially obscured, if corners stretch, if the whole view tilts, or if the lever resembles a full-width dashboard slider.

- [ ] **Step 3: Implement deterministic render entry points**

`scripts/assets/blender/render_family.py` must parse arguments after `--`, require `--output <directory>`, accept an optional `--scale` restricted to `1`, `0.75`, or `0.5` (default `1`), confirm `bpy.app.version_string` begins `4.5.11`, and render this immutable master table multiplied by that scale:

```py
OUTPUTS = {
    "Lens_Frame": ("frame.png", 4096, 4096),
    "Lens_Glass": ("glass.png", 4096, 4096),
    "Lens_Shadow": ("shadow.png", 4096, 4096),
    "Lever_Housing": ("lever-housing.png", 2048, 512),
    "Lever_Handle": ("lever-handle.png", 512, 512),
}
```

For every scene, set `render.engine = 'BLENDER_EEVEE_NEXT'`, transparent film, percentage 100, the listed dimensions, PNG RGBA, 8-bit color depth, straight alpha, sRGB display transform, fixed transparent world, and `scene.render.filepath`. Refuse a missing or extra required scene. Use one seed value `4511` for every procedural modifier or particle source that exposes a seed. Call `bpy.ops.render.render(write_still=True, scene=scene.name)`.

`scripts/assets/render-interface.sh` must:

1. accept only `central-lens`;
2. call `scripts/assets/check-blender.sh`;
3. remove and recreate `assets/interface/.staging/central-lens`;
4. invoke Blender in background/factory-startup mode with the committed `.blend` and render script;
5. run `npx tsx scripts/assets/promote-interface.ts --check-staging central-lens` without modifying committed files.

`scripts/assets/promote-interface.ts` must have two explicit modes and an optional `--scale` using the same restricted values as the Blender renderer:

- `--check-staging central-lens`: validate exact filenames, master dimensions multiplied by the requested scale, and nonempty alpha; do not write the repository.
- `--promote central-lens`: rerun the staging checks, copy the five files to `assets/interface/generated/central-lens`, compute source and output SHA-256 values with `sha256File`, create `assets/interface/manifest.json` from the exact contract in Task 2 with dimensions multiplied by the requested scale and `review: "candidate"`, write formatted JSON with a trailing newline, then run `validateInterfaceAssets` and exit nonzero on any error. On later promotions, it replaces only this family's dimensions and hashes and returns its review state to `candidate`.

- [ ] **Step 4: Render, inspect, and promote the candidate**

Run: `scripts/assets/render-interface.sh central-lens`

Expected: five dimension-valid PNG files in `assets/interface/.staging/central-lens` and no committed output changes.

Inspect the staged frame, glass, shadow, housing, and handle individually and as a contact sheet. If a layer violates the object contract in Step 2, edit `central-lens.blend` and rerender. Do not compensate in CSS.

Run: `npx tsx scripts/assets/promote-interface.ts --promote central-lens`

Expected: five committed generated files; the new manifest contains six computed hashes and no sentinel values; `review` is `candidate`; validation reports no errors.

- [ ] **Step 5: Run focused validation**

Run: `npx vitest run tests/assets/manifest.test.ts tests/assets/render-contract.test.ts`

Expected: all tests PASS.

Run: `npm run assets:validate`

Expected: exit 0 with `interface assets valid: 1 family, 5 outputs`.

- [ ] **Step 6: Commit the candidate source and derived exports**

```bash
git add assets/interface scripts/assets/render-interface.sh scripts/assets/blender/render_family.py scripts/assets/promote-interface.ts tests/assets/render-contract.test.ts
git commit -m "feat(game): author central lens asset family"
```

---

### Task 4: Game-owned lens geometry and timeline lever

**Files:**
- Create: `src/game/interface/lens-layout.ts`
- Create: `src/game/interface/timeline-lever.ts`
- Create: `tests/game/lens-layout.test.ts`
- Create: `tests/game/timeline-lever.test.ts`

**Interfaces:**
- Consumes: viewport dimensions and `nearestTimelineCursor` from `src/app/interact/scrubber.ts`.
- Produces: `lensLayout(width, height): LensLayout`; `leverHandleFraction(cursor, stateCount): number`; `mountTimelineLever(host, getTimeline, onMove): MountedTimelineLever`.

- [ ] **Step 1: Write failing pure tests**

```ts
// tests/game/lens-layout.test.ts
import { describe, expect, it } from 'vitest'
import { lensLayout } from '../../src/game/interface/lens-layout'

describe('Cursebreaker lens layout', () => {
  it.each([[1440, 900], [900, 1200], [640, 700]])('keeps a centered square lens within a 16px safe edge at %s×%s', (width, height) => {
    const layout = lensLayout(width, height)
    expect(layout.size).toBe(Math.min(height - 32, width - 32))
    expect(layout.left).toBe((width - layout.size) / 2)
    expect(layout.top).toBe((height - layout.size) / 2)
    expect(layout.glassSize).toBeCloseTo(layout.size * 0.73)
  })
})
```

```ts
// tests/game/timeline-lever.test.ts
import { describe, expect, it } from 'vitest'
import { leverHandleFraction, leverCursorAt } from '../../src/game/interface/timeline-lever'

describe('timeline lever presentation', () => {
  it('maps retained states to the full physical track', () => {
    expect(leverHandleFraction(0, 5)).toBe(0)
    expect(leverHandleFraction(2, 5)).toBe(0.5)
    expect(leverHandleFraction(4, 5)).toBe(1)
    expect(leverHandleFraction(0, 1)).toBe(0.5)
  })
  it('delegates pointer mapping to the established temporal rail rule', () => {
    expect(leverCursorAt(250, 100, 300, 4)).toBe(2)
  })
})
```

- [ ] **Step 2: Verify tests fail for missing modules**

Run: `npx vitest run tests/game/lens-layout.test.ts tests/game/timeline-lever.test.ts`

Expected: FAIL with missing module errors.

- [ ] **Step 3: Implement pure geometry and the lever DOM component**

```ts
// src/game/interface/lens-layout.ts
export type LensLayout = { readonly left: number; readonly top: number; readonly size: number; readonly glassInset: number; readonly glassSize: number }
export function lensLayout(width: number, height: number): LensLayout {
  const size = Math.max(1, Math.min(height - 32, width - 32))
  const glassInset = size * 0.135
  return { left: (width - size) / 2, top: (height - size) / 2, size, glassInset, glassSize: size - glassInset * 2 }
}
```

```ts
// public pure portion of src/game/interface/timeline-lever.ts
import { nearestTimelineCursor } from '../../app/interact/scrubber'
import type { GameTimeline } from '../session'

export const leverHandleFraction = (cursor: number, stateCount: number): number =>
  stateCount <= 1 ? 0.5 : cursor / (stateCount - 1)

export const leverCursorAt = (clientX: number, left: number, width: number, stateCount: number): number =>
  nearestTimelineCursor(clientX, left, width, stateCount)

export type MountedTimelineLever = { readonly element: HTMLElement; refresh(): void; dispose(): void }

export function mountTimelineLever(host: HTMLElement, getTimeline: () => GameTimeline, onMove: (cursor: number) => void): MountedTimelineLever {
  const element = document.createElement('div')
  element.className = 'curse-timeline'
  element.setAttribute('aria-label', 'Recorded seal states')
  const housing = document.createElement('img')
  housing.className = 'curse-timeline-housing curse-decoration'
  housing.src = new URL('../../../assets/interface/generated/central-lens/lever-housing.png', import.meta.url).href
  housing.alt = ''
  const rail = document.createElement('div')
  rail.className = 'curse-timeline-rail'
  rail.setAttribute('role', 'slider')
  rail.tabIndex = 0
  const handle = document.createElement('img')
  handle.className = 'curse-timeline-handle curse-decoration'
  handle.src = new URL('../../../assets/interface/generated/central-lens/lever-handle.png', import.meta.url).href
  handle.alt = ''
  rail.append(handle)
  element.append(housing, rail)
  host.append(element)
  let dragging = false
  const move = (event: PointerEvent): void => {
    const timeline = getTimeline()
    const rect = rail.getBoundingClientRect()
    onMove(leverCursorAt(event.clientX, rect.left, rect.width, timeline.states.length))
  }
  const down = (event: PointerEvent): void => { if (event.button === 0) { dragging = true; rail.setPointerCapture(event.pointerId); move(event) } }
  const moving = (event: PointerEvent): void => { if (dragging) move(event) }
  const up = (event: PointerEvent): void => { if (dragging) { dragging = false; if (rail.hasPointerCapture(event.pointerId)) rail.releasePointerCapture(event.pointerId) } }
  rail.addEventListener('pointerdown', down)
  rail.addEventListener('pointermove', moving)
  rail.addEventListener('pointerup', up)
  rail.addEventListener('pointercancel', up)
  const refresh = (): void => {
    const timeline = getTimeline()
    const fraction = leverHandleFraction(timeline.cursor, timeline.states.length)
    handle.style.setProperty('--curse-lever-position', String(fraction))
    rail.setAttribute('aria-valuemin', '0')
    rail.setAttribute('aria-valuemax', String(timeline.states.length - 1))
    rail.setAttribute('aria-valuenow', String(timeline.cursor))
  }
  refresh()
  return { element, refresh, dispose: () => { rail.removeEventListener('pointerdown', down); rail.removeEventListener('pointermove', moving); rail.removeEventListener('pointerup', up); rail.removeEventListener('pointercancel', up); element.remove() } }
}
```

- [ ] **Step 4: Run focused tests**

Run: `npx vitest run tests/game/lens-layout.test.ts tests/game/timeline-lever.test.ts tests/app/scrubber.test.ts`

Expected: all tests PASS; the established cursor-mapping tests remain green.

- [ ] **Step 5: Commit game presentation primitives**

```bash
git add src/game/interface/lens-layout.ts src/game/interface/timeline-lever.ts tests/game/lens-layout.test.ts tests/game/timeline-lever.test.ts
git commit -m "feat(game): add lens and lever presentation geometry"
```

---

### Task 5: Replace the assistant entry with the first real Cursebreaker shell

**Files:**
- Create: `src/game/interface/mount.ts`
- Create: `src/game/interface/index.ts`
- Modify: `src/game/index.ts`
- Replace: `app/main.ts`
- Replace: `app/index.html`
- Replace: `app/style.css`
- Modify: `package.json`
- Create: `tests/architecture/game-product-surface.test.ts`

**Interfaces:**
- Consumes: `openingCatalog`, `startPuzzle`, `applyGameStep`, `moveCursor`, `recordCompletion`, `ProofFrontViewport`, `DARK`, `defaultMotionPreferences`, lens layout, timeline lever, and the generated candidate assets.
- Produces: `mountCursebreaker(options: CursebreakerMountOptions): MountedCursebreaker`; one browser product rooted at `#cursebreaker`.

- [ ] **Step 1: Write the product-surface architecture test**

```ts
// tests/architecture/game-product-surface.test.ts
import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'

describe('game branch browser product', () => {
  it('mounts Cursebreaker without an assistant product entry', () => {
    const main = readFileSync('app/main.ts', 'utf8')
    const html = readFileSync('app/index.html', 'utf8')
    expect(main).toContain('mountCursebreaker')
    expect(main).not.toContain('mountShell')
    expect(html).toContain('<main id="cursebreaker"></main>')
    expect(html).not.toContain('id="chrome"')
    expect(html).not.toContain('Visual Proof Assistant')
  })
})
```

- [ ] **Step 2: Run the test and verify the old product entry fails it**

Run: `npx vitest run tests/architecture/game-product-surface.test.ts`

Expected: FAIL because `app/main.ts` contains `mountShell`.

- [ ] **Step 3: Implement `mountCursebreaker` around the existing backward viewport**

The mount creates exactly this DOM ownership:

```text
main#cursebreaker
  div.curse-lens-stage
    img.curse-lens-shadow.curse-decoration
    div.curse-lens-glass
      canvas#seal-canvas[aria-label="Seal under examination"]
    img.curse-lens-optics.curse-decoration
    div.curse-lens-frame.curse-decoration
    div.curse-timeline
```

`CursebreakerMountOptions` has `host: HTMLElement` and optional `initialPuzzle: PuzzleId`; default to `puzzleId('two-veils')`. The controller must:

- build `openingCatalog()` and refuse a locked non-default initial puzzle;
- own `GameProgress` and `GameSession` locally;
- construct `GameRuntimeAuthority` from the catalog and completed set;
- construct `ProofFrontViewport` with `side: 'backward'`, empty boundary, the catalog relation context plus an empty theorem map, `DARK`, and fuel 256;
- make `prepare(step)` call `applyGameStep` immediately but commit the returned session only in the closure supplied to `MotionCoordinator`;
- on commit, record first completion, reconcile the viewport, and refresh the lever;
- route Ctrl/Cmd+Z and Ctrl/Cmd+Shift+Z through `moveCursor`; no DOM undo or redo buttons exist;
- resize only from the glass element's `ResizeObserver` bounds and call `ProofFrontViewport.resize` with those exact bounds;
- apply `lensLayout(window.innerWidth, window.innerHeight)` to the stage on resize without altering canvas coordinates itself;
- run one `requestAnimationFrame` loop calling `viewport.frame(now)`;
- present refusals as a temporary pointer-adjacent `<output class="curse-refusal" role="alert">` without content-authored misconception metadata;
- return `dispose()` and a read-only debug seam containing puzzle id, timeline cursor/count, completed ids, lens rectangle, glass rectangle, and `ProofFrontViewport.debugState()`.

Do not copy the assistant shell state machine, library, import/export, edit mode, forward proving, fixed-side proving, theorem adoption, compass, or assistant chrome into this module.

- [ ] **Step 4: Replace the browser entry**

```ts
// app/main.ts
import { mountCursebreaker } from '../src/game'

const host = document.getElementById('cursebreaker')
if (!(host instanceof HTMLElement)) throw new Error("missing <main id='cursebreaker'>")

mountCursebreaker({ host })
```

```html
<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>Cursebreaker</title>
    <link rel="stylesheet" href="./style.css" />
  </head>
  <body>
    <main id="cursebreaker"></main>
    <script type="module" src="./main.ts"></script>
  </body>
</html>
```

Export the mount through `src/game/interface/index.ts` and `src/game/index.ts`.

Remove the assistant-only `preapp` and `pree2e` hooks from `package.json`; the game browser does not emit example theories before boot or browser tests. Retain `emit:theories` only as a kernel-development utility with no product entry point.

- [ ] **Step 5: Compose the candidate assets without input authority**

Replace `app/style.css`; do not preserve the assistant chrome selectors. The essential geometry is:

```css
:root { color-scheme: dark; background: #08090b; font-family: Inter, "Avenir Next", system-ui, sans-serif; }
html, body, #cursebreaker { width: 100%; height: 100%; margin: 0; overflow: hidden; }
body { background: radial-gradient(circle at 50% 42%, #171319 0, #0b0b0f 52%, #050608 100%); }
.curse-lens-stage { position: fixed; isolation: isolate; }
.curse-decoration { pointer-events: none !important; user-select: none; }
.curse-lens-shadow, .curse-lens-optics { position: absolute; inset: 0; width: 100%; height: 100%; object-fit: fill; }
.curse-lens-shadow { z-index: 0; }
.curse-lens-glass { position: absolute; z-index: 1; left: 13.5%; top: 13.5%; width: 73%; height: 73%; overflow: hidden; border-radius: 10%; background: #0e1013; }
#seal-canvas { display: block; width: 100%; height: 100%; touch-action: none; }
.curse-lens-optics { z-index: 2; opacity: .72; }
.curse-lens-frame { position: absolute; z-index: 3; inset: 0; box-sizing: border-box; border: min(13.7vw, 13.7vh) solid transparent; border-image-source: url('../assets/interface/generated/central-lens/frame.png'); border-image-slice: 560; border-image-width: 1; border-image-repeat: stretch; }
.curse-timeline { position: absolute; z-index: 4; left: 50%; bottom: 5.4%; width: 38%; height: 8%; transform: translateX(-50%); }
.curse-timeline-housing { position: absolute; inset: 0; width: 100%; height: 100%; object-fit: contain; }
.curse-timeline-rail { position: absolute; left: 11%; right: 11%; top: 26%; height: 48%; cursor: ew-resize; touch-action: none; }
.curse-timeline-handle { position: absolute; top: 50%; left: calc(var(--curse-lever-position) * 100%); width: 15%; height: auto; transform: translate(-50%, -50%); }
.curse-refusal { position: fixed; z-index: 20; max-width: 19rem; padding: .55rem .75rem; color: #ff9aa8; background: rgba(67, 18, 29, .94); border: 1px solid #fb7185; border-radius: 45% 48% 42% 12% / 52% 46% 45% 18%; box-shadow: 0 .4rem 1.4rem #0009; pointer-events: none; }
```

Set shadow and optics `src` attributes from Vite-resolved `new URL(..., import.meta.url)` values in `mount.ts`; frame uses the build-resolved CSS URL. Ensure all decorative `<img>` elements have `alt=""` and `aria-hidden="true"`.

- [ ] **Step 6: Run focused validation**

Run: `npx vitest run tests/architecture/game-product-surface.test.ts tests/game/lens-layout.test.ts tests/game/timeline-lever.test.ts tests/game/session.test.ts tests/app/proof-front.test.ts tests/app/moves.test.ts`

Expected: all tests PASS.

Run: `npm run typecheck`

Expected: exit 0.

Run: `npx vite build app --logLevel error`

Expected: production build succeeds and includes the five central-lens PNGs.

- [ ] **Step 7: Commit the one-product game shell**

```bash
git add app package.json src/game/interface src/game/index.ts tests/architecture/game-product-surface.test.ts
git commit -m "feat(game): mount opening seal in central lens"
```

---

### Task 6: Replace assistant-product browser tests with game evidence

**Files:**
- Delete: `e2e/app.spec.ts`
- Delete: `e2e/construction.spec.ts`
- Delete: `e2e/interaction.spec.ts`
- Create: `e2e/cursebreaker.spec.ts`
- Create: `scripts/assets/capture-central-lens.mjs`
- Modify: `package.json`

**Interfaces:**
- Consumes: real Vite production build, first opening artifact, `window.__cursebreakerDebug` only under `?debug`, and the candidate lens assets.
- Produces: functional E2E coverage and two review PNGs in ignored `test-results/central-lens-review/`.

- [ ] **Step 1: Add a debug seam without a second product path**

When `location.search` contains `debug`, assign the mount's read-only debug methods to `window.__cursebreakerDebug`. Expose only `state()`, `canvasToClient(worldPoint)`, and `dispose()`. No command may apply a move, unlock content, or mutate progression.

- [ ] **Step 2: Write the real game E2E tests**

`e2e/cursebreaker.spec.ts` must contain these tests:

1. **One-product boot:** title is Cursebreaker; `#cursebreaker`, `.curse-lens-stage`, and `#seal-canvas` are visible; assistant `#chrome`, `.vpa-compass`, library controls, forward proving, and import/export copy are absent.
2. **Straight-on responsive lens:** at 1440×900 and 700×820, stage width equals stage height within one pixel, every edge remains at least 15 pixels on screen, glass is centered, and the lever width is at most 40% of stage width.
3. **Decorative non-authority:** every `.curse-decoration` has `pointer-events: none`, no tabindex, empty alt if an image, and no accessibility role; the canvas remains the element at the center of the glass.
4. **Real opening content:** debug state names `two-veils`, exposes two cut regions and no theorem/library context, and canvas pixels are not uniformly the background color.
5. **Backward completion and retained history:** click the outer cut using debug geometry, open the existing contextual proof menu, choose the double-cut elimination action, then assert timeline cursor `1`, state count `2`, and completed contains `two-veils`. Drag the physical lever to its left endpoint and assert cursor `0`; drag right and assert cursor `1`. Ctrl+Z and Ctrl+Shift+Z traverse the same states. There are no undo/redo buttons.
6. **Asset load:** all decorative images have `naturalWidth > 0`; the browser reports no failed requests or uncaught errors.

The proof action itself must travel through `ProofFrontViewport` and `ProofMoveController`; the test may inspect debug geometry but may not call a debug mutation.

- [ ] **Step 3: Run E2E and repair only failures inside this milestone**

Run: `npm run e2e -- e2e/cursebreaker.spec.ts`

Expected: all six tests PASS.

Do not keep the old assistant E2E files as skipped tests, a second Vite root, or a hidden route. Their product assumptions were displaced; interaction-level unit tests under `tests/app` remain authoritative for shared proof controllers.

- [ ] **Step 4: Add deterministic review capture**

Create `scripts/assets/capture-central-lens.mjs` using Playwright's Chromium API. It launches the built preview URL supplied as its sole argument, captures `/` at 1440×900 to `test-results/central-lens-review/desktop.png`, then at 700×820 to `test-results/central-lens-review/compact.png`. It waits for `.curse-lens-stage`, `document.fonts.ready`, all `.curse-decoration` images to complete with positive natural width, and two animation frames before each screenshot.

Add `"assets:capture-lens": "node scripts/assets/capture-central-lens.mjs"` to `package.json`.

- [ ] **Step 5: Capture the real application**

Start: `npx vite preview app --port 4173 --strictPort`

Run in another command: `npm run assets:capture-lens -- http://127.0.0.1:4173`

Expected: `desktop.png` and `compact.png`, both showing the live opening seal, square lens, and compact lever.

- [ ] **Step 6: Commit functional browser evidence**

```bash
git add e2e package.json scripts/assets/capture-central-lens.mjs src/game/interface/mount.ts
git commit -m "test(game): validate central lens in real play"
```

---

### Task 7: Visual review gate and candidate iteration

**Files:**
- Modify as evidence requires: `assets/interface/source/blender/central-lens.blend`
- Regenerate as evidence requires: `assets/interface/generated/central-lens/*.png`
- Modify as evidence requires: `assets/interface/manifest.json`
- Modify only for compositional defects: `app/style.css`

**Interfaces:**
- Consumes: desktop and compact captures from Task 6.
- Produces: explicit user judgment on the actual asset family in game context.

- [ ] **Step 1: Present both captures to the user**

Show `test-results/central-lens-review/desktop.png` and `test-results/central-lens-review/compact.png`. State that they are the candidate central-lens family in the real game shell, not generated concept art, and identify that only the lens family is under review.

- [ ] **Step 2: Stop for user judgment**

Do not mark the manifest approved, begin folios/vellum/loupe assets, or claim visual completion before the user responds.

- [ ] **Step 3: If the user requests changes, repair the owning source**

- Material, construction, wear, reflection, lighting, mechanical proportion, or lever-object defects are fixed in `central-lens.blend` and rerendered.
- Nine-slice seams or incorrect stretch-safe areas are fixed in the Blender source and manifest insets.
- Responsive placement or scale defects are fixed in `lens-layout.ts` or `app/style.css`.
- Proof legibility is first fixed by reducing the glass layer in Blender; do not recolor or replace the proof canvas.

After each revision, rerun Task 3's asset checks, Task 6's E2E, rebuild, and recapture both viewports. Present the new pair. Repeat until approved or the user changes the design direction.

- [ ] **Step 4: Measure and select the smallest visually equivalent runtime export**

After the user accepts the material and construction direction, record the five committed PNG byte sizes and Chromium resource transfer sizes. Render uncommitted `0.75` and `0.5` variants into separate staging directories. Promote the 0.5 variant temporarily, update its manifest dimensions through the promoter, rebuild, rerun the six E2E tests at device scale factors 1 and 2, and capture both viewports. Compare it with the approved 4096-master capture at the same final viewport pixels.

Accept the 0.5 runtime variant only when all of these are true:

- every nine-slice seam remains invisible at desktop and compact sizes;
- fasteners, edge wear, and lever notches retain the approved construction reading;
- glass reflections remain smooth rather than banded;
- the proof canvas is pixel-identical because it is not part of the asset;
- Playwright reports no more than 0.5% of screenshot pixels differing by over 2/255 after masking the live proof canvas and animation-free background.

If 0.5 fails, test 0.75 by the same procedure. If 0.75 fails, retain scale 1. The selected scale becomes the only committed generated family, and the manifest records its actual dimensions and hashes. Delete unselected staging outputs. Present the final optimized desktop and compact captures and obtain confirmation that optimization did not change the approved appearance.

- [ ] **Step 5: Commit each reviewed revision separately**

```bash
git add assets/interface app/style.css src/game/interface/lens-layout.ts
git commit -m "refine(game): revise central lens candidate"
```

Only add files that actually changed.

---

### Task 8: Approve the family and run final non-physics verification

**Files:**
- Modify: `assets/interface/manifest.json`
- Append: the implementation turn's foundation record, whose unique scratch path was stated in that turn's first progress update

**Interfaces:**
- Consumes: explicit user approval from Task 7.
- Produces: approved central-lens family and a clean, backed-up branch.

- [ ] **Step 1: Change only the manifest review state**

Change `central-lens.review` from `candidate` to `approved`. Do not alter hashes unless the approved render files changed.

- [ ] **Step 2: Run authoritative final validation**

Run:

```bash
npm run assets:validate
npm run typecheck
npm test
npx vite build app --logLevel error
npm run e2e -- e2e/cursebreaker.spec.ts
git diff --check
git status --short
```

Expected:

- asset validator: 1 family and 5 outputs valid;
- typecheck: exit 0;
- ordinary tests: all pass with physics battery excluded by default;
- production build: succeeds;
- Cursebreaker E2E: all pass;
- diff check: no errors;
- status: only the deliberate manifest approval and any final conformance documentation are pending.

Do **not** run `npm run test:physics`.

- [ ] **Step 3: Prove the prohibited scope stayed untouched**

Run:

```bash
git diff --name-only a55a682..HEAD | rg '^(src/view/(engine|relax|forces)|tests/view/.*physics|vitest\.physics)' && exit 1 || true
git diff --name-only HEAD~1..HEAD
```

Expected: the first command prints nothing; the final approval commit contains only the manifest and conformance record.

- [ ] **Step 4: Append foundation conformance**

Record implemented owners, assistant app-entry displacement, committed source and generated structures, browser/test evidence, user visual approval, exact validation results, and evidence that no competing assistant route, decorative input path, raster proof surface, or physics change remains.

- [ ] **Step 5: Commit and push the approved milestone**

```bash
git add assets/interface/manifest.json
git commit -m "feat(game): approve central lens production family"
git push
```

- [ ] **Step 6: Report the milestone boundary**

Report the approved lens source path, five runtime assets, real browser entry, test/build results, commit, and pushed branch. State that surrounding desk work remains intentionally unopened and requires its own reviewed asset milestone.
