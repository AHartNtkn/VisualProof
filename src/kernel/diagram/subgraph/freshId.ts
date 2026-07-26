const MINT_CALLBACK: unique symbol = Symbol('mint-callback')

type IdNamespaceReservation = ReadonlySet<string> & {
  readonly [MINT_CALLBACK]?: (id: string) => void
}

export type IdReservation = {
  readonly regions: IdNamespaceReservation
  readonly nodes: IdNamespaceReservation
  readonly wires: IdNamespaceReservation
}

/** Exact construction-order history, recorded before normalization. */
export type IdMintLog = {
  readonly regions: readonly string[]
  readonly nodes: readonly string[]
  readonly wires: readonly string[]
}

export type IdMintRecorder = {
  readonly regions: string[]
  readonly nodes: string[]
  readonly wires: string[]
}

export function createIdMintRecorder(): IdMintRecorder {
  return { regions: [], nodes: [], wires: [] }
}

export function freezeIdMintLog(recorder: IdMintRecorder): IdMintLog {
  return Object.freeze({
    regions: Object.freeze([...recorder.regions]),
    nodes: Object.freeze([...recorder.nodes]),
    wires: Object.freeze([...recorder.wires]),
  })
}

export function appendIdMintLog(
  recorder: IdMintRecorder,
  log: IdMintLog,
): void {
  recorder.regions.push(...log.regions)
  recorder.nodes.push(...log.nodes)
  recorder.wires.push(...log.wires)
}

function captureNamespace(
  base: IdNamespaceReservation | undefined,
  record: (id: string) => void,
): IdNamespaceReservation {
  const captured = new Set(base ?? []) as Set<string> & IdNamespaceReservation
  const inherited = base?.[MINT_CALLBACK]
  Object.defineProperty(captured, MINT_CALLBACK, {
    value: inherited === undefined
      ? record
      : (id: string) => {
          inherited(id)
          record(id)
        },
  })
  return captured
}

/** Add a receipt observer without changing the exclusion namespace. */
export function withIdMintCapture(
  base: IdReservation | undefined,
  recorder: IdMintRecorder,
): IdReservation {
  return {
    regions: captureNamespace(base?.regions, (id) => recorder.regions.push(id)),
    nodes: captureNamespace(base?.nodes, (id) => recorder.nodes.push(id)),
    wires: captureNamespace(base?.wires, (id) => recorder.wires.push(id)),
  }
}

function extendNamespace(
  base: IdNamespaceReservation | undefined,
  additions: readonly string[],
): IdNamespaceReservation {
  const extended = new Set([
    ...(base ?? []),
    ...additions,
  ]) as Set<string> & IdNamespaceReservation
  const inherited = base?.[MINT_CALLBACK]
  if (inherited !== undefined) {
    Object.defineProperty(extended, MINT_CALLBACK, { value: inherited })
  }
  return extended
}

/** Immutably reserve additional IDs while preserving any mint observer. */
export function extendIdReservation(
  base: IdReservation | undefined,
  additions: IdMintLog,
): IdReservation {
  return {
    regions: extendNamespace(base?.regions, additions.regions),
    nodes: extendNamespace(base?.nodes, additions.nodes),
    wires: extendNamespace(base?.wires, additions.wires),
  }
}

/** Deterministic collision-dodging id: base, then base_0, base_1, … */
export function freshId(
  taken: ReadonlySet<string>,
  base: string,
  reserved: IdNamespaceReservation = new Set(),
): string {
  const mint = (id: string): string => {
    reserved[MINT_CALLBACK]?.(id)
    return id
  }
  if (!taken.has(base) && !reserved.has(base)) return mint(base)
  for (let k = 0; ; k++) {
    const candidate = `${base}_${k}`
    if (!taken.has(candidate) && !reserved.has(candidate)) return mint(candidate)
  }
}
