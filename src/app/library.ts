import type { ProofContext } from '../kernel/proof/step'
import type { Theorem } from '../kernel/proof/theorem'
import { checkTheorem } from '../kernel/proof/theorem'
import type { Theory } from '../kernel/proof/store'
import { loadTheory } from '../kernel/proof/store'
import type { BootContext } from './boot'
import { mergeTheories } from './boot'

/**
 * The library: the user's explicit view over available theory files and what
 * they have chosen to load. Boot fills `manifest` with the available file names
 * and nothing is loaded; the working ProofContext is whatever `rebuild` merges
 * from the LOADED entries plus session-adopted theorems. There is no auto-load:
 * an empty library rebuilds to an empty context, which is honest.
 */
export type AvailableEntry = { readonly file: string; readonly status: 'available' }
export type LoadedEntry = {
  readonly file: string
  readonly status: 'loaded'
  readonly theory: Theory
  readonly ctx: ProofContext
}
export type LibraryEntry = AvailableEntry | LoadedEntry

export type Library = {
  /** The manifest file names, in manifest order — the set that returns to
   *  'available' on unload (a foreign loaded file is removed instead). */
  readonly manifest: readonly string[]
  /** Every known file as an entry, in display order (manifest first, then any
   *  foreign files loaded from disk). */
  readonly entries: readonly LibraryEntry[]
  /** Theorems proven and adopted this session — their own group, citable and
   *  replayable, contributing to the merged context on every rebuild. */
  readonly adopted: readonly Theorem[]
}

/** A fresh library over a manifest: every file available, nothing loaded, no
 *  adopted theorems. Rebuilds to the empty context. */
export function mkLibrary(manifest: readonly string[]): Library {
  return {
    manifest,
    entries: manifest.map((file) => ({ file, status: 'available' })),
    adopted: [],
  }
}

/**
 * Load a file's JSON through loadTheory (the only verifying road) and mark its
 * entry loaded; a file absent from the manifest is appended as a foreign loaded
 * entry. The candidate state is rebuilt before it is returned, so a merge
 * conflict (duplicate theorem/relation name, clashing definition body) throws
 * loudly and the CALLER keeps the prior library — the load leaves no partial
 * state behind.
 */
export function loadEntry(lib: Library, file: string, json: unknown): Library {
  const { theory, ctx } = loadTheory(json)
  const loaded: LoadedEntry = { file, status: 'loaded', theory, ctx }
  const idx = lib.entries.findIndex((e) => e.file === file)
  const entries = idx >= 0
    ? lib.entries.map((e, i) => (i === idx ? loaded : e))
    : [...lib.entries, loaded]
  const next: Library = { ...lib, entries }
  rebuild(next) // conflict check: throws before the new state is adopted
  return next
}

/**
 * Unload a loaded entry: a manifest file returns to 'available'; a foreign file
 * is dropped entirely (it has no available form). Removal never conflicts —
 * mergeTheories is additive, so the remainder rebuilds deterministically.
 */
export function unloadEntry(lib: Library, file: string): Library {
  const idx = lib.entries.findIndex((e) => e.file === file)
  if (idx < 0) throw new Error(`no library entry for '${file}'`)
  if (lib.entries[idx]!.status !== 'loaded') throw new Error(`library entry '${file}' is not loaded`)
  const entries = lib.manifest.includes(file)
    ? lib.entries.map((e, i) => (i === idx ? { file, status: 'available' as const } : e))
    : lib.entries.filter((_, i) => i !== idx)
  return { ...lib, entries }
}

/**
 * Record a session-adopted theorem in the Session group. The candidate state is
 * rebuilt first, so an adoption that would collide with a loaded theorem name,
 * or that no longer checks against the merged context, throws loudly and the
 * caller keeps the prior library.
 */
export function adoptEntry(lib: Library, thm: Theorem): Library {
  const next: Library = { ...lib, adopted: [...lib.adopted, thm] }
  rebuild(next)
  return next
}

/**
 * Merge every LOADED entry (mergeTheories) and then layer the session-adopted
 * theorems on top, verifying each against the growing context in adoption order.
 * The result is the working ProofContext the shell binds live. Any conflict
 * refuses loudly.
 */
export function rebuild(lib: Library): BootContext {
  const loaded = lib.entries
    .filter((e): e is LoadedEntry => e.status === 'loaded')
    .map((e) => ({ theory: e.theory, ctx: e.ctx }))
  const base = mergeTheories(loaded)
  if (lib.adopted.length === 0) return base
  const theorems = new Map(base.ctx.theorems)
  for (const thm of lib.adopted) {
    if (theorems.has(thm.name)) {
      throw new Error(`library conflict: adopted theorem '${thm.name}' duplicates a loaded theorem`)
    }
    checkTheorem(thm, { definitions: base.ctx.definitions, theorems, relations: base.ctx.relations })
    theorems.set(thm.name, thm)
  }
  return { ...base, ctx: { ...base.ctx, theorems } }
}
