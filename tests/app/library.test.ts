import { describe, it, expect } from 'vitest'
import { parseTerm } from '../../src/kernel/term/parse'
import { mkDiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { theoryToJson, loadTheory } from '../../src/kernel/proof/store'
import type { Theorem } from '../../src/kernel/proof/theorem'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import type { DiagramWithBoundary } from '../../src/kernel/diagram/boundary'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { exploreForm } from '../../src/kernel/diagram/canonical/explore'
import { applyRelFold } from '../../src/kernel/rules/reldef'
import { emptyDiagram } from '../../src/app/edit'
import { spawnTermNode } from '../../src/kernel/diagram/spawn'
import { defineRelation } from '../../src/app/define'
import type { LibraryEntry } from '../../src/app/library'
import { emptyLibrary, reconcile, loadEntry, unloadEntry, adoptEntry, defineEntry, rebuild } from '../../src/app/library'
import { sheetBody, emptyCtx } from './relationFixture'

const p = (s: string) => parseTerm(s)
const fregeJson = () => theoryToJson(buildFregeTheory())
const lambdaJson = () => theoryToJson(buildLambdaTheory())
const status = (entries: readonly LibraryEntry[]) => entries.map((e) => [e.file, e.status])

/** A reflexive theorem (lhs === rhs, zero steps) cites nothing, so it checks
 *  against any context — the minimal adoptable object. */
function trivTheorem(name: string): Theorem {
  const e0 = emptyDiagram()
  const { diagram } = spawnTermNode(e0, e0.root, p('\\x. x'))
  const dwb = mkDiagramWithBoundary(diagram, [])
  return { name, lhs: dwb, rhs: dwb, actions: [] }
}

/** A closed arity-1 relation body (one term node, its free-var line the
 *  boundary). No ref nodes, so its refs resolve against any context. */
function trivRelation(): DiagramWithBoundary {
  const e0 = emptyDiagram()
  const { diagram, node } = spawnTermNode(e0, e0.root, p('y'))
  const bound = Object.keys(diagram.wires).find((w) =>
    diagram.wires[w]!.endpoints.some((ep) => ep.node === node && ep.port.kind === 'freeVar'),
  )!
  return mkDiagramWithBoundary(diagram, [bound])
}

/** An arity-1 relation body whose ONLY node is a ref to `nat`: its ref resolves
 *  iff a theory providing `nat` (arity 1) is in the merged context. Used to pin
 *  the ref-resolution lifecycle — a defined relation depending on a loaded one. */
function relationCitingNat(): DiagramWithBoundary {
  const b = new DiagramBuilder()
  const r = b.ref(b.root, 'nat', 1)
  const w = b.wire(b.root, [{ node: r, port: { kind: 'arg', index: 0 } }])
  return mkDiagramWithBoundary(b.build(), [w])
}

function relationCiting(name: string): DiagramWithBoundary {
  const builder = new DiagramBuilder()
  const ref = builder.ref(builder.root, name, 1)
  const wire = builder.wire(builder.root, [{ node: ref, port: { kind: 'arg', index: 0 } }])
  return mkDiagramWithBoundary(builder.build(), [wire])
}

describe('emptyLibrary', () => {
  it('knows nothing: no folder, no entries, no adopted; rebuilds to the empty context', () => {
    const lib = emptyLibrary()
    expect(lib.folder).toEqual([])
    expect(lib.entries).toEqual([])
    expect(lib.adopted).toEqual([])
    const boot = rebuild(lib)
    expect([...boot.ctx.theorems.keys()]).toEqual([])
    expect(Object.keys(boot.relations)).toEqual([])
  })
})

describe('reconcile (Open folder / Refresh)', () => {
  it('lists every folder file as available, uniformly, and records the folder', () => {
    const lib = reconcile(emptyLibrary(), ['frege.json', 'lambda.json'])
    expect(lib.folder).toEqual(['frege.json', 'lambda.json'])
    expect(status(lib.entries)).toEqual([
      ['frege.json', 'available'],
      ['lambda.json', 'available'],
    ])
  })

  it('preserves a loaded entry across a refresh and lists the rest available', () => {
    let lib = reconcile(emptyLibrary(), ['frege.json', 'lambda.json'])
    lib = loadEntry(lib, 'frege.json', fregeJson())
    lib = reconcile(lib, ['frege.json', 'lambda.json']) // refresh
    expect(status(lib.entries)).toEqual([
      ['frege.json', 'loaded'],
      ['lambda.json', 'available'],
    ])
  })

  it('drops an available file that has disappeared from the folder', () => {
    let lib = reconcile(emptyLibrary(), ['frege.json', 'lambda.json'])
    lib = reconcile(lib, ['frege.json']) // lambda.json removed on disk
    expect(status(lib.entries)).toEqual([['frege.json', 'available']])
  })

  it('keeps a one-off loaded file even when it is not in the folder', () => {
    let lib = loadEntry(emptyLibrary(), 'mine.json', lambdaJson()) // opened directly, no folder
    lib = reconcile(lib, ['frege.json']) // then a folder is opened
    expect(status(lib.entries)).toEqual([
      ['frege.json', 'available'],
      ['mine.json', 'loaded'],
    ])
  })
})

describe('loadEntry / rebuild', () => {
  it('flips a folder file to loaded and merges its content into rebuild', () => {
    let lib = reconcile(emptyLibrary(), ['frege.json'])
    lib = loadEntry(lib, 'frege.json', fregeJson())
    expect(lib.entries.find((e) => e.file === 'frege.json')!.status).toBe('loaded')
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('plusAssoc')).toBe(true)
    expect(boot.relations['nat']).toBeDefined()
  })

  it('appends a directly-opened file (not in any folder) as a loaded entry', () => {
    const lib = loadEntry(emptyLibrary(), 'mine.json', lambdaJson())
    expect(status(lib.entries)).toEqual([['mine.json', 'loaded']])
    expect(rebuild(lib).ctx.theorems.has('fixedPoint')).toBe(true)
  })

  it('refuses a duplicate-theorem conflict loudly and leaves the state unchanged', () => {
    const lib = loadEntry(reconcile(emptyLibrary(), ['frege.json', 'frege2.json']), 'frege.json', fregeJson())
    expect(() => loadEntry(lib, 'frege2.json', fregeJson()))
      .toThrowError(/theory merge conflict: duplicate theorem 'plusAssoc'/)
    expect(lib.entries.find((e) => e.file === 'frege2.json')!.status).toBe('available')
  })

  it('propagates a malformed-theory refusal from loadTheory (the only road)', () => {
    const bad = { format: 'visual-proof-theory', version: 1, relations: 'nope', theorems: [] }
    expect(() => loadEntry(emptyLibrary(), 'x.json', bad)).toThrowError(/malformed theory JSON/)
  })
})

describe('unloadEntry', () => {
  it('returns a folder file to available and rebuilds from the remainder', () => {
    let lib = reconcile(emptyLibrary(), ['frege.json', 'lambda.json'])
    lib = loadEntry(lib, 'frege.json', fregeJson())
    lib = loadEntry(lib, 'lambda.json', lambdaJson())
    lib = unloadEntry(lib, 'lambda.json')
    expect(lib.entries.find((e) => e.file === 'lambda.json')!.status).toBe('available')
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('plusAssoc')).toBe(true) // frege still loaded
    expect(boot.ctx.theorems.has('fixedPoint')).toBe(false) // lambda gone
  })

  it('drops a directly-opened (non-folder) file entirely on unload', () => {
    let lib = loadEntry(emptyLibrary(), 'mine.json', lambdaJson())
    lib = unloadEntry(lib, 'mine.json')
    expect(lib.entries).toEqual([])
  })

  it('refuses to unload a file that is not loaded', () => {
    const lib = reconcile(emptyLibrary(), ['frege.json'])
    expect(() => unloadEntry(lib, 'frege.json')).toThrowError(/not loaded/)
    expect(() => unloadEntry(lib, 'ghost.json')).toThrowError(/no library entry/)
  })
})

describe('adoptEntry', () => {
  it('records an adopted theorem in its own group and merges it into rebuild', () => {
    let lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    lib = adoptEntry(lib, trivTheorem('myLemma'))
    expect(lib.adopted.map((t) => t.name)).toEqual(['myLemma'])
    const boot = rebuild(lib)
    expect(boot.ctx.theorems.has('myLemma')).toBe(true)
    expect(boot.ctx.theorems.has('plusAssoc')).toBe(true)
  })

  it('adopts onto an empty library too (no file loaded)', () => {
    const lib = adoptEntry(emptyLibrary(), trivTheorem('solo'))
    expect([...rebuild(lib).ctx.theorems.keys()]).toEqual(['solo'])
  })

  it('refuses an adopted name that duplicates a loaded theorem, leaving state unchanged', () => {
    const lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    expect(() => adoptEntry(lib, trivTheorem('plusAssoc')))
      .toThrowError(/adopted theorem 'plusAssoc' duplicates a loaded theorem/)
    expect(lib.adopted).toEqual([])
  })
})

describe('defineEntry', () => {
  it('records a defined relation in its group and merges it into ctx.relations and the record', () => {
    let lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    lib = defineEntry(lib, 'myRel', trivRelation())
    expect(lib.definedRelations.map((r) => r.name)).toEqual(['myRel'])
    const boot = rebuild(lib)
    expect(boot.ctx.relations.has('myRel')).toBe(true)
    expect(boot.relations['myRel']).toBeDefined()
    expect(boot.relations['nat']).toBeDefined() // loaded relation still present
  })

  it('defines onto an empty library too (no file loaded)', () => {
    const lib = defineEntry(emptyLibrary(), 'solo', trivRelation())
    expect(Object.keys(rebuild(lib).relations)).toEqual(['solo'])
  })

  it('survives unloading an unrelated file — the defined relation persists across rebuild', () => {
    let lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    lib = defineEntry(lib, 'myRel', trivRelation())
    lib = unloadEntry(lib, 'frege.json') // folder-less open → dropped
    const boot = rebuild(lib)
    expect(boot.relations['myRel']).toBeDefined()
    expect(boot.relations['nat']).toBeUndefined() // frege gone
  })

  it('refuses a defined name that duplicates a loaded relation, leaving state unchanged', () => {
    const lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    expect(() => defineEntry(lib, 'nat', trivRelation()))
      .toThrowError(/defined relation 'nat' duplicates a loaded or defined relation/)
    expect(lib.definedRelations).toEqual([])
  })

  it('refuses a defined name that duplicates a loaded theorem (one namespace)', () => {
    const lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    expect(() => defineEntry(lib, 'plusAssoc', trivRelation()))
      .toThrowError(/defined relation 'plusAssoc' duplicates a theorem name/)
    expect(lib.definedRelations).toEqual([])
  })

  it('refuses adopting a theorem whose name collides with a defined relation', () => {
    const lib = defineEntry(emptyLibrary(), 'shared', trivRelation())
    expect(() => adoptEntry(lib, trivTheorem('shared')))
      .toThrowError(/adopted theorem 'shared' duplicates a loaded theorem or a relation/)
  })

  it('refuses defining a relation whose name collides with an ADOPTED theorem', () => {
    // The reverse of the line above: a name adopted as a theorem this session is
    // still taken for a relation (one namespace), and defineEntry's pre-check
    // must catch it before the definedRelations list grows.
    const lib = adoptEntry(emptyLibrary(), trivTheorem('shared'))
    expect(() => defineEntry(lib, 'shared', trivRelation()))
      .toThrowError(/duplicates a (loaded theorem or a relation|theorem name)/)
    expect(lib.definedRelations).toEqual([])
  })
})

describe('namespace integrity across the load boundary (define-then-load)', () => {
  // The defineEntry block covers define-AFTER-load; this is the reverse order —
  // a file loaded into a session that already defines a colliding relation. The
  // load must refuse, not silently shadow, and leave the file unloaded.
  it('refuses LOADING a file whose relation name a session-defined relation already holds', () => {
    const lib = defineEntry(emptyLibrary(), 'nat', trivRelation()) // 'nat' now defined
    expect(() => loadEntry(lib, 'frege.json', fregeJson())) // frege also defines 'nat'
      .toThrowError(/defined relation 'nat' duplicates a loaded or defined relation/)
    // The file is not listed and the working context still has only the session 'nat'.
    expect(lib.entries).toEqual([])
    expect(Object.keys(rebuild(lib).relations)).toEqual(['nat'])
  })

  it('refuses LOADING a file whose THEOREM name a session-defined relation already holds', () => {
    const lib = defineEntry(emptyLibrary(), 'plusAssoc', trivRelation()) // relation named for frege's theorem
    expect(() => loadEntry(lib, 'frege.json', fregeJson()))
      .toThrowError(/defined relation 'plusAssoc' duplicates a theorem name/)
    expect(lib.entries).toEqual([])
  })
})

describe('ref-resolution lifecycle: a defined relation citing a LOADED relation', () => {
  it('resolves the defined body while the cited file is loaded', () => {
    let lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    lib = defineEntry(lib, 'usesNat', relationCitingNat())
    const boot = rebuild(lib)
    expect(boot.relations['usesNat']).toBeDefined()
    expect(boot.relations['nat']).toBeDefined()
  })

  it('refuses to unload the cited file, keeping it loaded and the context resolvable', () => {
    // Every OTHER library mutator (load/adopt/define) rebuilds as an atomic
    // pre-check before returning; unloadEntry must do the same, or unloading a
    // file a defined relation still cites strands that ref while the library
    // silently records the file as gone.
    let lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    lib = defineEntry(lib, 'usesNat', relationCitingNat())
    expect(() => unloadEntry(lib, 'frege.json'))
      .toThrowError(/unknown relation 'nat'/)
    // atomic: the entry is still loaded and the working context still resolves.
    expect(lib.entries.find((e) => e.file === 'frege.json')!.status).toBe('loaded')
    expect(() => rebuild(lib)).not.toThrow()
  })

  it('permits unloading once the citing relation is not present (no false positive)', () => {
    // A defined relation with no cross-file ref never blocks an unload.
    let lib = loadEntry(emptyLibrary(), 'frege.json', fregeJson())
    lib = defineEntry(lib, 'standalone', trivRelation())
    expect(() => unloadEntry(lib, 'frege.json')).not.toThrow()
  })
})

describe('session relation prefix verification', () => {
  it('accepts an earlier session definition and preserves definition order', () => {
    let lib = defineEntry(emptyLibrary(), 'Base', trivRelation())
    lib = defineEntry(lib, 'Alias', relationCiting('Base'))
    expect(Object.keys(rebuild(lib).relations)).toEqual(['Base', 'Alias'])
  })

  it('atomically rejects self, forward, and cyclic session definitions', () => {
    const empty = emptyLibrary()
    expect(() => defineEntry(empty, 'Self', relationCiting('Self'))).toThrowError(/unknown relation 'Self'/)
    expect(empty.definedRelations).toEqual([])

    expect(() => defineEntry(empty, 'Forward', relationCiting('Later'))).toThrowError(/unknown relation 'Later'/)
    expect(empty.definedRelations).toEqual([])

    const cyclic = {
      ...empty,
      definedRelations: [
        { name: 'Left', relation: relationCiting('Right') },
        { name: 'Right', relation: relationCiting('Left') },
      ],
    }
    expect(() => rebuild(cyclic)).toThrowError(/relation 'Left' body: reference node .* unknown relation 'Right'/)
    expect(empty.definedRelations).toEqual([])
  })
})

describe('session-defined relation round-trips through Save → loadTheory (fresh library)', () => {
  it('folds/unfolds identically and preserves argument ORDER after a JSON round-trip', () => {
    // Define an asymmetric arity-2 relation, save it the way the shell saves
    // (theoryToJson over the rebuilt relations), then reload through the ONLY
    // verifying road (loadTheory) into a fresh context.
    const { d, sel, wY, wZ } = sheetBody()
    const lib = defineEntry(emptyLibrary(), 'R', defineRelation(d, sel, [wY, wZ], 'R', emptyCtx, {}).relation)
    const saved = rebuild(lib).relations
    const json = theoryToJson({ relations: saved, theorems: [] })

    const reloaded = loadTheory(json).ctx.relations
    const R2 = reloaded.get('R')!
    expect(R2).toBeDefined()
    // Bodies are form-equal across the round-trip.
    expect(exploreForm(R2.diagram)).toBe(exploreForm(saved['R']!.diagram))
    // Argument order survived: folding the original body with the SAVED pick
    // order [wY,wZ] matches the reloaded relation; the reversed order does not —
    // the same order-sensitivity defineRelation established, now through JSON.
    const rels = new Map([['R', R2]])
    expect(() => applyRelFold(d, sel, 'R', [wY, wZ], rels)).not.toThrow()
    expect(() => applyRelFold(d, sel, 'R', [wZ, wY], rels)).toThrow(/does not match relation 'R'/)
  })
})
