import { application, bound, free, lambda, type Term } from './term'

/** Free slots used by a term, once each, in structural first-occurrence order. */
export function freeSlots(term: Term): number[] {
  const slots: number[] = []
  const seen = new Set<number>()
  const visit = (current: Term): void => {
    switch (current.kind) {
      case 'bound': return
      case 'free':
        if (!seen.has(current.slot)) {
          seen.add(current.slot)
          slots.push(current.slot)
        }
        return
      case 'lambda':
        visit(current.body)
        return
      case 'application':
        visit(current.fn)
        visit(current.argument)
    }
  }
  visit(term)
  return slots
}

/** Apply one total positional renaming to every free occurrence in a term. */
export function mapFreeSlots(term: Term, mapping: readonly number[]): Term {
  switch (term.kind) {
    case 'bound': return bound(term.index)
    case 'free': {
      const slot = mapping[term.slot]
      if (slot === undefined || !Number.isSafeInteger(slot) || slot < 0) {
        throw new Error(`free slot ${term.slot} has no valid mapped position`)
      }
      return free(slot)
    }
    case 'lambda': return lambda(mapFreeSlots(term.body, mapping))
    case 'application':
      return application(
        mapFreeSlots(term.fn, mapping),
        mapFreeSlots(term.argument, mapping),
      )
  }
}

/** Compact a term onto the unique physical carriers used by its free support. */
export function compactFreeInterface<T>(
  term: Term,
  carriersBySlot: readonly T[],
): {
  readonly term: Term
  readonly carriers: readonly T[]
  readonly sourceSlots: readonly number[]
} {
  const mapping: number[] = []
  const carriers: T[] = []
  const sourceSlots: number[] = []
  const compactByCarrier = new Map<T, number>()
  for (const slot of freeSlots(term)) {
    const carrier = carriersBySlot[slot]
    if (carrier === undefined) {
      throw new Error(`free slot ${slot} has no interface carrier`)
    }
    let compact = compactByCarrier.get(carrier)
    if (compact === undefined) {
      compact = carriers.length
      compactByCarrier.set(carrier, compact)
      carriers.push(carrier)
      sourceSlots.push(slot)
    }
    mapping[slot] = compact
  }
  return { term: mapFreeSlots(term, mapping), carriers, sourceSlots }
}

export function defaultFreeIdentifier(slot: number): string {
  if (!Number.isSafeInteger(slot) || slot < 0) {
    throw new RangeError(`free slot must be a non-negative safe integer, got ${slot}`)
  }
  return `f${slot}`
}

export function freeIdentifierSlot(identifier: string): number | null {
  const match = /^f(0|[1-9][0-9]*)$/u.exec(identifier)
  return match === null ? null : Number(match[1])
}
