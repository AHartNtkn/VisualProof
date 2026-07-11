/**
 * Synthetic relation library for the spawn-browser round: the four real Peano
 * relations plus ~130 plausible fakes across namespaces, so hierarchy and
 * search face a realistic population (flat menus visibly stop working).
 */
export type LibEntry = { readonly ns: string; readonly name: string; readonly arity: number }

const SPEC: Record<string, string[]> = {
  arith: ['add', 'mul', 'sub', 'div', 'mod', 'pow', 'gcd', 'lcm', 'abs', 'sign', 'min', 'max', 'square', 'double', 'half', 'even', 'odd', 'prime', 'factorial', 'fib'],
  list: ['cons', 'nil', 'append', 'reverse', 'length', 'map', 'filter', 'fold', 'head', 'tail', 'last', 'take', 'drop', 'zip', 'elem', 'sorted', 'permutation', 'sublist'],
  logic: ['and', 'or', 'not', 'implies', 'iff', 'xor', 'nand', 'nor', 'taut', 'sat', 'valid'],
  set: ['member', 'subset', 'union', 'inter', 'diff', 'powerset', 'empty', 'disjoint', 'partition', 'singleton', 'pair'],
  graph: ['edge', 'path', 'cycle', 'connected', 'tree', 'forest', 'clique', 'bipartite', 'planar', 'degree', 'adjacent', 'reachable'],
  order: ['le', 'lt', 'ge', 'gt', 'between', 'minimal', 'maximal', 'chain', 'antichain', 'wellfounded', 'dense', 'total'],
  string: ['concat', 'prefix', 'suffix', 'substr', 'palindrome', 'anagram', 'matches', 'contains'],
  tree: ['leaf', 'node', 'height', 'balanced', 'binary', 'complete', 'subtree', 'mirror'],
  geom: ['point', 'line', 'circle', 'collinear', 'parallel', 'perpendicular', 'congruent', 'similar', 'inside', 'tangent'],
  rel: ['refl', 'symm', 'trans', 'equiv', 'functional', 'injective', 'surjective', 'bijective', 'inverse', 'compose', 'closure'],
}

export function syntheticLibrary(): LibEntry[] {
  const out: LibEntry[] = [
    { ns: 'peano', name: 'zero', arity: 1 },
    { ns: 'peano', name: 'succ', arity: 2 },
    { ns: 'peano', name: 'plus', arity: 3 },
    { ns: 'peano', name: 'nat', arity: 1 },
  ]
  for (const [ns, names] of Object.entries(SPEC)) {
    // deterministic arity spread 1–4 across entries (synthetic data, not logic)
    names.forEach((name, i) => out.push({ ns, name, arity: 1 + ((i * 7 + ns.length) % 4) }))
  }
  return out
}

export const libId = (e: LibEntry): string => `${e.ns}/${e.name}`

/** Case-insensitive substring search over ns/name, ranked by match position
    then by entry length (earlier and tighter matches first). */
export function searchLibrary(entries: readonly LibEntry[], query: string): LibEntry[] {
  const q = query.trim().toLowerCase()
  if (q === '') return []
  const scored: { e: LibEntry; pos: number; len: number }[] = []
  for (const e of entries) {
    const id = libId(e).toLowerCase()
    const pos = id.indexOf(q)
    if (pos >= 0) scored.push({ e, pos, len: id.length })
  }
  scored.sort((a, b) => a.pos - b.pos || a.len - b.len || (libId(a.e) < libId(b.e) ? -1 : 1))
  return scored.map((s) => s.e)
}

/** Session-local recency (most recent first, deduped). */
export function mkRecents(cap: number): { list(): LibEntry[]; note(e: LibEntry): void } {
  const recent: LibEntry[] = []
  return {
    list: () => [...recent],
    note: (e) => {
      const i = recent.findIndex((r) => libId(r) === libId(e))
      if (i >= 0) recent.splice(i, 1)
      recent.unshift(e)
      if (recent.length > cap) recent.pop()
    },
  }
}
