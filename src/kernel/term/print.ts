import type { Term } from './term'

type Context = 'top' | 'applicationFn' | 'applicationArgument'

/** Deterministically print a term, consulting optional parser-boundary names for free slots. */
export function printTerm(term: Term, freeIdentifiers?: readonly string[]): string {
  const freeName = (slot: number): string => {
    if (freeIdentifiers === undefined) return `f${slot}`
    const identifier = freeIdentifiers[slot]
    if (identifier === undefined) {
      throw new Error(`free slot ${slot} has no supplied identifier`)
    }
    return identifier
  }
  const taken = new Set<string>()
  const collect = (current: Term): void => {
    switch (current.kind) {
      case 'free':
        taken.add(freeName(current.slot))
        return
      case 'lambda':
        collect(current.body)
        return
      case 'application':
        collect(current.fn)
        collect(current.argument)
        return
      case 'bound':
        return
    }
  }
  collect(term)
  return print(term, [], taken, freeName, 'top')
}

function print(
  term: Term,
  environment: readonly string[],
  taken: ReadonlySet<string>,
  freeName: (slot: number) => string,
  context: Context,
): string {
  switch (term.kind) {
    case 'bound': {
      const identifier = environment[environment.length - 1 - term.index]
      if (identifier === undefined) {
        throw new Error(`unbound de Bruijn index ${term.index} at depth ${environment.length}; term is malformed`)
      }
      return identifier
    }
    case 'free': return freeName(term.slot)
    case 'lambda': {
      let identifier = `x${environment.length}`
      while (taken.has(identifier) || environment.includes(identifier)) identifier = `_${identifier}`
      const body = print(term.body, [...environment, identifier], taken, freeName, 'top')
      const rendered = `\\${identifier}. ${body}`
      return context === 'top' ? rendered : `(${rendered})`
    }
    case 'application': {
      const fn = print(term.fn, environment, taken, freeName, 'applicationFn')
      const argument = print(term.argument, environment, taken, freeName, 'applicationArgument')
      const rendered = `${fn} ${argument}`
      return context === 'applicationArgument' ? `(${rendered})` : rendered
    }
  }
}
