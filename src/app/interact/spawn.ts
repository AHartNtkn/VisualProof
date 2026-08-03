import type { Diagram, RegionId, WireId } from '../../kernel/diagram/diagram'
import type { Vec2 } from '../../view/vec'

export const UNQUALIFIED_GROUP_LABEL = 'Unqualified'
const DEFAULT_RECENTS_LIMIT = 5
const SEARCH_RESULT_LIMIT = 14

export type SpawnRelationBody = { readonly boundary: readonly unknown[] }
export type SpawnRelationSource = Iterable<readonly [string, SpawnRelationBody]>

export type SpawnRelation = {
  readonly defId: string
  readonly namespace: string | null
  readonly leaf: string
  readonly arity: number
}

export type SpawnNamespaceGroup = {
  readonly namespace: string | null
  readonly label: string
  readonly entries: readonly SpawnRelation[]
}

export type SpawnCatalog = {
  readonly entries: readonly SpawnRelation[]
  readonly groups: readonly SpawnNamespaceGroup[]
  readonly byId: ReadonlyMap<string, SpawnRelation>
}

export type AtomHeadOption = {
  readonly wire: WireId
  readonly arity: number
  readonly position: number
  readonly total: number
}

/** Visible relational wires that can own the head of a new atom. */
export function atomHeadOptions(
  diagram: Diagram,
  region: RegionId,
): readonly AtomHeadOption[] {
  const found: Array<{ readonly wire: WireId; readonly arity: number }> = []
  let current: RegionId | undefined = region
  for (;;) {
    const value: Diagram['regions'][string] | undefined = diagram.regions[current]
    if (value === undefined) throw new Error(`unknown region '${current}'`)
    const here = Object.entries(diagram.wires)
      .filter(([, wire]) => wire.scope === current && wire.sig.kind === 'rel')
      .sort(([left], [right]) => left.localeCompare(right))
    for (const [wire, value] of here) {
      if (value.sig.kind === 'rel') found.push({ wire, arity: value.sig.args.length })
    }
    if (value.kind === 'sheet') break
    current = value.parent
  }
  return Object.freeze(found.map((option, index) => Object.freeze({
    ...option,
    position: index + 1,
    total: found.length,
  })))
}

export type SpawnInvocation = {
  readonly screen: Vec2
  readonly world: Vec2
  readonly region: RegionId
}

export type SpawnRefRequest = {
  readonly defId: string
  readonly arity: number
  readonly invocation: SpawnInvocation
}

export type SpawnAtomRequest = {
  readonly wire: WireId
  readonly arity: number
  readonly invocation: SpawnInvocation
}

export type SpawnCascadeOptions = {
  readonly host: HTMLElement
  readonly spawnRef: (request: SpawnRefRequest) => boolean | void
  readonly spawnAtom: (request: SpawnAtomRequest) => boolean | void
  readonly headWireColor: (wire: WireId) => string
  readonly hoverHeadWire?: (wire: WireId | null) => void
  readonly openChanged?: (open: boolean) => void
  readonly recentsLimit?: number
}

function compareText(left: string, right: string): number {
  return left < right ? -1 : left > right ? 1 : 0
}

function relationParts(defId: string): {
  readonly namespace: string | null
  readonly leaf: string
} {
  const separator = defId.lastIndexOf('/')
  return separator < 0
    ? { namespace: null, leaf: defId }
    : { namespace: defId.slice(0, separator), leaf: defId.slice(separator + 1) }
}

export function buildSpawnCatalog(relations: SpawnRelationSource): SpawnCatalog {
  const byId = new Map<string, SpawnRelation>()
  for (const [defId, body] of relations) {
    const entry = Object.freeze({
      defId,
      ...relationParts(defId),
      arity: body.boundary.length,
    })
    const previous = byId.get(defId)
    if (previous !== undefined) {
      if (previous.arity !== entry.arity) {
        throw new Error(`relation id '${defId}' has conflicting arities`)
      }
      continue
    }
    byId.set(defId, entry)
  }
  const entries = [...byId.values()].sort((left, right) =>
    compareText(left.defId, right.defId))
  const grouped = new Map<string | null, SpawnRelation[]>()
  for (const entry of entries) {
    const group = grouped.get(entry.namespace) ?? []
    group.push(entry)
    grouped.set(entry.namespace, group)
  }
  const namespaces = [...grouped.keys()].sort((left, right) => {
    if (left === null) return right === null ? 0 : -1
    if (right === null) return 1
    return compareText(left, right)
  })
  return Object.freeze({
    entries: Object.freeze(entries),
    groups: Object.freeze(namespaces.map((namespace): SpawnNamespaceGroup =>
      Object.freeze({
        namespace,
        label: namespace === null
          ? UNQUALIFIED_GROUP_LABEL
          : namespace === '' ? '/' : namespace,
        entries: Object.freeze([...(grouped.get(namespace) ?? [])]),
      }))),
    byId,
  })
}

export function searchSpawnCatalog(
  catalog: SpawnCatalog,
  query: string,
): readonly SpawnRelation[] {
  const needle = query.trim().toLowerCase()
  if (needle === '') return []
  return catalog.entries
    .map((entry) => ({
      entry,
      position: entry.defId.toLowerCase().indexOf(needle),
    }))
    .filter((result) => result.position >= 0)
    .sort((left, right) =>
      left.position - right.position
      || left.entry.defId.length - right.entry.defId.length
      || compareText(left.entry.defId, right.entry.defId))
    .map((result) => result.entry)
}

export class SpawnRecents {
  readonly #limit: number
  readonly #ids: string[] = []

  constructor(limit = DEFAULT_RECENTS_LIMIT) {
    if (!Number.isInteger(limit) || limit < 0) {
      throw new RangeError('recent spawn limit must be a nonnegative integer')
    }
    this.#limit = limit
  }

  note(defId: string): void {
    const previous = this.#ids.indexOf(defId)
    if (previous >= 0) this.#ids.splice(previous, 1)
    this.#ids.unshift(defId)
    if (this.#ids.length > this.#limit) this.#ids.length = this.#limit
  }

  list(catalog: SpawnCatalog): readonly SpawnRelation[] {
    return this.#ids.flatMap((defId) => {
      const entry = catalog.byId.get(defId)
      return entry === undefined ? [] : [entry]
    })
  }
}

export function snapshotSpawnInvocation(invocation: SpawnInvocation): SpawnInvocation {
  return Object.freeze({
    screen: Object.freeze({ ...invocation.screen }),
    world: Object.freeze({ ...invocation.world }),
    region: invocation.region,
  })
}

export class SpawnCascade {
  readonly #host: HTMLElement
  readonly #document: Document
  readonly #spawnRef: SpawnCascadeOptions['spawnRef']
  readonly #spawnAtom: SpawnCascadeOptions['spawnAtom']
  readonly #headWireColor: SpawnCascadeOptions['headWireColor']
  readonly #hoverHeadWire: SpawnCascadeOptions['hoverHeadWire']
  readonly #openChanged: SpawnCascadeOptions['openChanged']
  readonly #recents: SpawnRecents
  #menu: HTMLDivElement | null = null
  #backdrop: HTMLDivElement | null = null
  #invocation: SpawnInvocation | null = null
  #disposed = false

  constructor(options: SpawnCascadeOptions) {
    this.#host = options.host
    this.#document = options.host.ownerDocument
    this.#spawnRef = options.spawnRef
    this.#spawnAtom = options.spawnAtom
    this.#headWireColor = options.headWireColor
    this.#hoverHeadWire = options.hoverHeadWire
    this.#openChanged = options.openChanged
    this.#recents = new SpawnRecents(options.recentsLimit)
  }

  get isOpen(): boolean { return this.#menu !== null }
  get invocation(): SpawnInvocation | null { return this.#invocation }

  open(
    invocation: SpawnInvocation,
    relations: SpawnRelationSource,
    atomHeads: readonly AtomHeadOption[],
  ): void {
    if (this.#disposed) throw new Error('spawn cascade is disposed')
    const snapshot = snapshotSpawnInvocation(invocation)
    const catalog = buildSpawnCatalog(relations)
    const heads = Object.freeze([...atomHeads])
    this.close()
    this.#invocation = snapshot

    const menu = this.#document.createElement('div')
    menu.className = 'vpa-spawn-cascade'
    menu.setAttribute('role', 'menu')
    const viewport = this.#document.defaultView
    const maxLeft = Math.max(0, (viewport?.innerWidth ?? snapshot.screen.x + 240) - 240)
    const maxTop = Math.max(0, (viewport?.innerHeight ?? snapshot.screen.y + 320) - 320)
    menu.style.left = `${Math.max(0, Math.min(snapshot.screen.x, maxLeft))}px`
    menu.style.top = `${Math.max(0, Math.min(snapshot.screen.y, maxTop))}px`
    const backdrop = this.#document.createElement('div')
    backdrop.className = 'vpa-spawn-backdrop'
    backdrop.addEventListener('pointerdown', () => this.close())

    const search = this.#document.createElement('input')
    search.className = 'vpa-spawn-search'
    search.type = 'search'
    search.autocomplete = 'off'
    search.placeholder = `search references → '${snapshot.region}'`
    search.setAttribute('aria-label', 'Search relation references to spawn')
    const listing = this.#document.createElement('div')
    listing.className = 'vpa-spawn-listing'
    menu.append(search, listing)
    this.#menu = menu
    this.#backdrop = backdrop
    this.#host.append(backdrop, menu)
    this.#openChanged?.(true)

    const current = (): boolean =>
      this.#menu === menu && this.#invocation === snapshot
    const row = (
      label: string,
      hint: string,
      pick: (() => void) | null,
    ): HTMLElement => {
      const item = this.#document.createElement(pick === null ? 'div' : 'button')
      item.className = pick === null ? 'vpa-spawn-heading' : 'vpa-spawn-row'
      item.textContent = hint === '' ? label : `${label} ${hint}`
      if (pick !== null) item.addEventListener('click', pick)
      return item
    }
    const pickRef = (entry: SpawnRelation): void => {
      if (!current()) return
      const accepted = this.#spawnRef({
        defId: entry.defId,
        arity: entry.arity,
        invocation: snapshot,
      })
      if (accepted === false) return
      this.#recents.note(entry.defId)
      this.close()
    }
    const refRow = (entry: SpawnRelation): HTMLElement => {
      const item = row(entry.defId, `/${entry.arity}`, () => pickRef(entry))
      item.dataset.defId = entry.defId
      return item
    }
    const headRow = (entry: AtomHeadOption): HTMLElement => {
      const label = entry.total === 1
        ? 'Atom on visible relation'
        : `Atom on relation ${entry.position}`
      const item = row(label, `/${entry.arity}`, () => {
        if (!current()) return
        const accepted = this.#spawnAtom({
          wire: entry.wire,
          arity: entry.arity,
          invocation: snapshot,
        })
        if (accepted !== false) this.close()
      })
      item.dataset.wire = entry.wire
      item.style.borderLeft = `6px solid ${this.#headWireColor(entry.wire)}`
      item.addEventListener('pointerenter', () => this.#hoverHeadWire?.(entry.wire))
      item.addEventListener('pointerleave', () => this.#hoverHeadWire?.(null))
      return item
    }
    const render = (): void => {
      const query = search.value.trim()
      const refs = query === ''
        ? this.#recents.list(catalog)
        : searchSpawnCatalog(catalog, query).slice(0, SEARCH_RESULT_LIMIT)
      const content: HTMLElement[] = []
      if (heads.length > 0 && query === '') {
        content.push(row('Atoms', '', null), ...heads.map(headRow))
      }
      if (refs.length > 0) {
        content.push(row(query === '' ? 'Recent references' : 'References', '', null))
        content.push(...refs.map(refRow))
      } else if (query === '' && catalog.entries.length > 0) {
        content.push(row('References', '', null), ...catalog.entries.slice(0, SEARCH_RESULT_LIMIT).map(refRow))
      }
      if (content.length === 0) content.push(row('No structural spawn is available', '', null))
      listing.replaceChildren(...content)
    }
    search.addEventListener('input', render)
    search.addEventListener('keydown', (event) => {
      event.stopPropagation()
      if (event.key === 'Escape') {
        event.preventDefault()
        this.close()
      } else if (event.key === 'Enter') {
        event.preventDefault()
        const first = searchSpawnCatalog(catalog, search.value)[0]
        if (first !== undefined) pickRef(first)
      }
    })
    render()
    queueMicrotask(() => {
      if (current()) search.focus()
    })
  }

  close(): boolean {
    this.#hoverHeadWire?.(null)
    if (this.#menu === null) return false
    this.#menu.remove()
    this.#backdrop?.remove()
    this.#menu = null
    this.#backdrop = null
    this.#invocation = null
    this.#openChanged?.(false)
    return true
  }

  escape(): boolean { return this.close() }

  outside(target: Node | null): boolean {
    const menu = this.#menu
    if (menu === null || (target !== null && menu.contains(target))) return false
    return this.close()
  }

  dispose(): void {
    if (this.#disposed) return
    this.close()
    this.#disposed = true
  }
}
