import type { ProofContext } from '../kernel/proof/context'
import { assertProofContext, verifyTheory } from '../kernel/proof/context'
import type { Theorem } from '../kernel/proof/theorem'
import type { DiagramWithBoundary } from '../kernel/diagram/boundary'
import type { Theory } from '../kernel/proof/store'
import { loadTheory } from '../kernel/proof/store'
import type { BootContext } from './boot'

/**
 * The library: a uniform view over theory files. There is NO privileged origin
 * — a file listed from a workspace folder and a file opened directly are the
 * same kind of entry, with the same Load/Unload affordance. The working context
 * is whatever `rebuild` merges from the LOADED entries plus the session-adopted
 * theorems; an empty library rebuilds to the empty context.
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
  /** File names in the currently-open workspace folder (empty when none is
   *  open). Set by `reconcile` on Open-folder/Refresh; used only to decide
   *  whether an unloaded file remains listed (folder file) or disappears
   *  (a one-off opened file). It carries no privilege — it is just the folder
   *  contents. */
  readonly folder: readonly string[]
  /** Every known file as an entry, in display order. */
  readonly entries: readonly LibraryEntry[]
  /** Theorems proven and adopted this session — their own group, citable and
   *  replayable, contributing to the merged context on every rebuild. */
  readonly adopted: readonly Theorem[]
  /** Relations named from the live sheet this session, in definition order —
   *  the same Session group as adopted theorems, foldable/citable and merged
   *  into the working context (and thus into a Save) on every rebuild. */
  readonly definedRelations: readonly DefinedRelation[]
}

export type DefinedRelation = { readonly name: string; readonly relation: DiagramWithBoundary }

/** A library that knows nothing: no folder, no entries, no adopted content.
 *  Rebuilds to the empty context — the honest empty boot. */
export function emptyLibrary(): Library {
  return { folder: [], entries: [], adopted: [], definedRelations: [] }
}

/**
 * Reconcile the library against a workspace folder's file listing (Open folder
 * or Refresh). Loaded entries persist untouched (their content lives in memory,
 * independent of disk); every folder file that is not currently loaded is listed
 * as available; a folder file that IS loaded stays loaded. One-off loaded files
 * that are absent from the folder remain listed too, so opening a folder never
 * silently drops what the user already loaded. Display order: folder order
 * first, then any loaded files not in the folder.
 */
export function reconcile(lib: Library, folderFiles: readonly string[]): Library {
  const loadedByName = new Map<string, LoadedEntry>()
  for (const e of lib.entries) if (e.status === 'loaded') loadedByName.set(e.file, e)
  const entries: LibraryEntry[] = []
  const placed = new Set<string>()
  for (const file of folderFiles) {
    if (placed.has(file)) continue
    placed.add(file)
    entries.push(loadedByName.get(file) ?? { file, status: 'available' })
  }
  for (const e of loadedByName.values()) {
    if (!placed.has(e.file)) entries.push(e)
  }
  return { ...lib, folder: folderFiles, entries }
}

/**
 * Load a file's JSON through loadTheory (the only verifying road) and mark its
 * entry loaded; a file not already listed is appended as a loaded entry. The
 * candidate state is rebuilt before it is returned, so a merge conflict
 * (duplicate theorem/relation name, clashing definition body) throws loudly and
 * the CALLER keeps the prior library — the load leaves no partial state behind.
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
 * Unload a loaded entry: a file still present in the workspace folder returns to
 * 'available'; a file not in the folder (opened one-off) is dropped entirely.
 * Removal never introduces a NAME conflict (mergeTheories is additive), but it
 * CAN strand a session-defined relation whose body cites a relation the unloaded
 * file provided — so the candidate is rebuilt first, exactly like load/adopt/
 * define, and a broken ref throws loudly and the CALLER keeps the prior library.
 */
export function unloadEntry(lib: Library, file: string): Library {
  const idx = lib.entries.findIndex((e) => e.file === file)
  if (idx < 0) throw new Error(`no library entry for '${file}'`)
  if (lib.entries[idx]!.status !== 'loaded') throw new Error(`library entry '${file}' is not loaded`)
  const entries = lib.folder.includes(file)
    ? lib.entries.map((e, i) => (i === idx ? { file, status: 'available' as const } : e))
    : lib.entries.filter((_, i) => i !== idx)
  const next: Library = { ...lib, entries }
  rebuild(next) // conflict check: a defined relation's now-unresolvable ref throws before adoption
  return next
}

/**
 * Record a session-adopted theorem in the Session group. The candidate state is
 * rebuilt first, so an adoption that would collide with a loaded theorem name,
 * or that no longer checks against the merged context, throws loudly and the
 * caller keeps the prior library.
 */
export function adoptEntry(lib: Library, thm: Theorem): Library {
  const current = rebuild(lib).ctx
  if (current.theorems.has(thm.name) || current.relations.has(thm.name)) {
    throw new Error(`library conflict: adopted theorem '${thm.name}' duplicates a loaded theorem or a relation`)
  }
  const next: Library = { ...lib, adopted: [...lib.adopted, thm] }
  rebuild(next)
  return next
}

/**
 * Record a session-defined relation in the Session group. The candidate state is
 * rebuilt first, so a definition that would collide with a loaded/defined
 * relation name, a theorem name, or that references a relation no longer present
 * throws loudly and the caller keeps the prior library.
 */
export function defineEntry(lib: Library, name: string, relation: DiagramWithBoundary): Library {
  const current = rebuild(lib).ctx
  if (current.relations.has(name)) {
    throw new Error(`library conflict: defined relation '${name}' duplicates a loaded or defined relation`)
  }
  if (current.theorems.has(name)) {
    throw new Error(`library conflict: defined relation '${name}' duplicates a theorem name`)
  }
  const next: Library = { ...lib, definedRelations: [...lib.definedRelations, { name, relation }] }
  rebuild(next)
  return next
}

/**
 * Merge every LOADED entry (mergeTheories), layer the session-defined relations,
 * then the session-adopted theorems — each verified against the growing context.
 * The result is the working ProofContext the shell binds live. Any conflict
 * (name collision across the single relation+theorem namespace, or a defined
 * relation whose refs no longer resolve) refuses loudly.
 */
export function rebuild(lib: Library): BootContext {
  const loaded = lib.entries
    .filter((e): e is LoadedEntry => e.status === 'loaded')
  for (const entry of loaded) assertProofContext(entry.ctx)
  const relations: Record<string, DiagramWithBoundary> = {}
  const theorems: Theorem[] = []
  const loadedRelations = new Set<string>()
  const loadedTheorems = new Set<string>()
  for (const entry of loaded) {
    for (const name of entry.ctx.theorems.keys()) {
      if (loadedTheorems.has(name)) throw new Error(`theory merge conflict: duplicate theorem '${name}'`)
      loadedTheorems.add(name)
    }
    for (const name of entry.ctx.relations.keys()) {
      if (loadedRelations.has(name)) throw new Error(`theory merge conflict: duplicate relation '${name}'`)
      loadedRelations.add(name)
    }
  }
  for (const name of loadedRelations) {
    if (loadedTheorems.has(name)) throw new Error(`theory merge conflict: '${name}' names both a relation and theorem`)
  }
  for (const entry of loaded) {
    for (const [name, relation] of entry.ctx.relations) relations[name] = relation
  }
  const allTheoremNames = new Set(loadedTheorems)
  for (const theorem of lib.adopted) allTheoremNames.add(theorem.name)
  const definedNames = new Set<string>()
  for (const { name, relation } of lib.definedRelations) {
    if (loadedRelations.has(name) || definedNames.has(name)) {
      throw new Error(`library conflict: defined relation '${name}' duplicates a loaded or defined relation`)
    }
    if (allTheoremNames.has(name)) {
      throw new Error(`library conflict: defined relation '${name}' duplicates a theorem name`)
    }
    definedNames.add(name)
    relations[name] = relation
  }
  for (const entry of loaded) theorems.push(...entry.ctx.theorems.values())
  const adoptedNames = new Set<string>()
  for (const theorem of lib.adopted) {
    if (loadedTheorems.has(theorem.name) || adoptedNames.has(theorem.name)
      || loadedRelations.has(theorem.name) || definedNames.has(theorem.name)) {
      throw new Error(`library conflict: adopted theorem '${theorem.name}' duplicates a loaded theorem or a relation`)
    }
    adoptedNames.add(theorem.name)
    theorems.push(theorem)
  }
  return { ctx: verifyTheory({ relations, theorems }), relations }
}
