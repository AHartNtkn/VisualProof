import type { Diagram, RegionId } from '../../../../kernel/diagram/diagram'
import type { Vec2 } from '../../../../view/vec'

export const UNQUALIFIED_GROUP_LABEL = 'Unqualified'
const DEFAULT_RECENTS_LIMIT = 5
const SEARCH_RESULT_LIMIT = 14

export type SpawnRelationBody = { readonly boundary: readonly unknown[] }
export type SpawnRelationSource = Iterable<readonly [string, SpawnRelationBody]>

export type SpawnRelation = {
  /** Exact relation identifier submitted to the edit layer. */
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

export type SpawnBoundPredicateOption = {
  readonly binder: RegionId
  readonly arity: number
  readonly position: number
  readonly total: number
}

export function boundPredicateOptions(d: Diagram, region: RegionId): readonly SpawnBoundPredicateOption[] {
  const found: { binder: RegionId; arity: number }[] = []
  let current = region
  for (;;) {
    const value = d.regions[current]
    if (value === undefined) throw new Error(`unknown region '${current}'`)
    if (value.kind === 'bubble') found.push({ binder: current, arity: value.arity })
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

export type SpawnTermRequest = {
  readonly source: string
  readonly invocation: SpawnInvocation
}

export type SpawnRelationRequest = {
  readonly defId: string
  readonly arity: number
  readonly invocation: SpawnInvocation
}

export type SpawnBoundPredicateRequest = {
  readonly binder: RegionId
  readonly invocation: SpawnInvocation
}

export type SpawnCascadeOptions = {
  readonly host: HTMLElement
  /** Return false to keep the cascade open after a refused edit. */
  readonly spawnTerm: (request: SpawnTermRequest) => boolean | void
  /** Return false to keep the cascade open after a refused edit. */
  readonly spawnRelation: (request: SpawnRelationRequest) => boolean | void
  /** Return false to keep the cascade open after a refused edit. */
  readonly spawnBoundPredicate: (request: SpawnBoundPredicateRequest) => boolean | void
  /** Presentation color derived from the renderer's authoritative binder hue. */
  readonly binderColor: (binder: RegionId) => string
  /** View-only binder emphasis. Null clears every cascade-owned emphasis. */
  readonly hoverBinder?: (binder: RegionId | null) => void
  readonly openChanged?: (open: boolean) => void
  readonly recentsLimit?: number
}

function compareText(a: string, b: string): number {
  return a < b ? -1 : a > b ? 1 : 0
}

function relationParts(defId: string): { readonly namespace: string | null; readonly leaf: string } {
  const separator = defId.lastIndexOf('/')
  return separator < 0
    ? { namespace: null, leaf: defId }
    : { namespace: defId.slice(0, separator), leaf: defId.slice(separator + 1) }
}

/** Snapshot the current real relation map into deterministic browse groups. */
export function buildSpawnCatalog(relations: SpawnRelationSource): SpawnCatalog {
  const byId = new Map<string, SpawnRelation>()
  for (const [defId, body] of relations) {
    const parts = relationParts(defId)
    const entry = Object.freeze({ defId, ...parts, arity: body.boundary.length })
    const previous = byId.get(defId)
    if (previous !== undefined) {
      if (previous.arity !== entry.arity) throw new Error(`relation id '${defId}' has conflicting arities`)
      continue
    }
    byId.set(defId, entry)
  }

  const entries = [...byId.values()].sort((a, b) => compareText(a.defId, b.defId))
  const grouped = new Map<string | null, SpawnRelation[]>()
  for (const entry of entries) {
    const group = grouped.get(entry.namespace) ?? []
    group.push(entry)
    grouped.set(entry.namespace, group)
  }
  const namespaces = [...grouped.keys()].sort((a, b) => {
    if (a === null) return b === null ? 0 : -1
    if (b === null) return 1
    return compareText(a, b)
  })
  const groups = namespaces.map((namespace): SpawnNamespaceGroup => Object.freeze({
    namespace,
    label: namespace === null ? UNQUALIFIED_GROUP_LABEL : namespace === '' ? '/' : namespace,
    entries: Object.freeze([...(grouped.get(namespace) ?? [])]),
  }))
  return Object.freeze({
    entries: Object.freeze(entries),
    groups: Object.freeze(groups),
    byId,
  })
}

/** Case-insensitive substring search over the complete exact identifier. */
export function searchSpawnCatalog(catalog: SpawnCatalog, query: string): readonly SpawnRelation[] {
  const needle = query.trim().toLowerCase()
  if (needle === '') return []
  return catalog.entries
    .map((entry) => ({ entry, lower: entry.defId.toLowerCase() }))
    .map(({ entry, lower }) => ({ entry, position: lower.indexOf(needle), length: lower.length }))
    .filter((result) => result.position >= 0)
    .sort((a, b) => a.position - b.position
      || a.length - b.length
      || compareText(a.entry.defId, b.entry.defId))
    .map((result) => result.entry)
}

/** Session-local recency: exact identifiers, most recent first, deduped. */
export class SpawnRecents {
  readonly #limit: number
  readonly #ids: string[] = []

  constructor(limit = DEFAULT_RECENTS_LIMIT) {
    if (!Number.isInteger(limit) || limit < 0) throw new RangeError('recent spawn limit must be a nonnegative integer')
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

/**
 * Disposable contextual cascade. The host application owns gesture routing:
 * it calls `open` for a still secondary click and forwards Escape/outside
 * presses through the explicit methods below. This class installs no canvas,
 * window, or document listeners.
 */
export class SpawnCascade {
  readonly #host: HTMLElement
  readonly #document: Document
  readonly #spawnTerm: SpawnCascadeOptions['spawnTerm']
  readonly #spawnRelation: SpawnCascadeOptions['spawnRelation']
  readonly #spawnBoundPredicate: SpawnCascadeOptions['spawnBoundPredicate']
  readonly #binderColor: SpawnCascadeOptions['binderColor']
  readonly #hoverBinder: SpawnCascadeOptions['hoverBinder']
  readonly #openChanged: SpawnCascadeOptions['openChanged']
  readonly #recents: SpawnRecents
  #menu: HTMLDivElement | null = null
  #backdrop: HTMLDivElement | null = null
  #invocation: SpawnInvocation | null = null
  #disposed = false

  constructor(options: SpawnCascadeOptions) {
    this.#host = options.host
    this.#document = options.host.ownerDocument
    this.#spawnTerm = options.spawnTerm
    this.#spawnRelation = options.spawnRelation
    this.#spawnBoundPredicate = options.spawnBoundPredicate
    this.#binderColor = options.binderColor
    this.#hoverBinder = options.hoverBinder
    this.#openChanged = options.openChanged
    this.#recents = new SpawnRecents(options.recentsLimit)
  }

  get isOpen(): boolean { return this.#menu !== null }
  get invocation(): SpawnInvocation | null { return this.#invocation }

  open(
    invocation: SpawnInvocation,
    relations: SpawnRelationSource,
    boundPredicates: readonly SpawnBoundPredicateOption[],
  ): void {
    if (this.#disposed) throw new Error('spawn cascade is disposed')
    const snapshot = snapshotSpawnInvocation(invocation)
    const catalog = buildSpawnCatalog(relations)
    const predicates = Object.freeze([...boundPredicates])
    this.close()
    this.#invocation = snapshot

    const menu = this.#document.createElement('div')
    menu.className = 'vpa-spawn-cascade'
    menu.setAttribute('role', 'menu')
    const viewport = this.#document.defaultView
    const maxLeft = Math.max(0, (viewport?.innerWidth ?? snapshot.screen.x + 360) - 360)
    const maxTop = Math.max(0, (viewport?.innerHeight ?? snapshot.screen.y + 320) - 320)
    menu.style.cssText = `position:fixed;left:${Math.max(0, Math.min(snapshot.screen.x, maxLeft))}px;top:${Math.max(0, Math.min(snapshot.screen.y, maxTop))}px;z-index:71;display:flex;align-items:flex-start;font:13px system-ui,sans-serif`

    const backdrop = this.#document.createElement('div')
    backdrop.className = 'vpa-spawn-backdrop'
    backdrop.style.cssText = 'position:fixed;inset:0;z-index:70;background:transparent'
    backdrop.addEventListener('pointerdown', () => this.close())

    const column = this.#document.createElement('div')
    column.className = 'vpa-spawn-column'
    column.style.cssText = 'width:220px;overflow:hidden;border:1.5px solid #d97706;border-radius:8px;background:#fff;box-shadow:0 4px 16px #0003'
    const search = this.#document.createElement('input')
    search.className = 'vpa-spawn-search'
    search.type = 'search'
    search.autocomplete = 'off'
    search.placeholder = `search relations → '${snapshot.region}'`
    search.setAttribute('aria-label', 'Search relations to spawn')
    search.style.cssText = 'width:100%;box-sizing:border-box;padding:7px 10px;border:0;border-bottom:1px solid #e7e5e4;outline:0;font:13px system-ui,sans-serif'
    const listing = this.#document.createElement('div')
    listing.className = 'vpa-spawn-listing'
    listing.style.cssText = 'max-height:270px;overflow-y:auto'
    column.append(search, listing)

    const submenu = this.#document.createElement('div')
    submenu.className = 'vpa-spawn-submenu'
    submenu.style.cssText = 'display:none;width:190px;max-height:300px;margin-left:2px;overflow-y:auto;border:1px solid #a8a29e;border-radius:8px;background:#fff;box-shadow:0 4px 16px #0002'
    menu.append(column, submenu)
    this.#menu = menu
    this.#backdrop = backdrop
    this.#host.append(backdrop, menu)
    this.#openChanged?.(true)

    let termMode = false
    const current = (): boolean => this.#menu === menu && this.#invocation === snapshot

    const row = (label: string, hint: string, pick: (() => void) | null): HTMLElement => {
      const item = this.#document.createElement(pick === null ? 'div' : 'button')
      item.className = 'vpa-spawn-row'
      if (pick !== null) (item as HTMLButtonElement).type = 'button'
      item.style.cssText = `display:flex;width:100%;box-sizing:border-box;justify-content:space-between;gap:6px;padding:6px 10px;border:0;background:#fff;text-align:left;font:13px system-ui,sans-serif;${pick === null ? 'color:#78716c' : 'cursor:pointer'}`
      const name = this.#document.createElement('span')
      name.textContent = label
      const meta = this.#document.createElement('span')
      meta.textContent = hint
      meta.style.color = '#a8a29e'
      item.append(name, meta)
      if (pick !== null) {
        item.addEventListener('pointerenter', () => { item.style.background = '#fef3c7' })
        item.addEventListener('pointerleave', () => { item.style.background = '#fff' })
        item.addEventListener('click', pick)
      }
      return item
    }

    const heading = (text: string): HTMLElement => {
      const item = this.#document.createElement('div')
      item.className = 'vpa-spawn-heading'
      item.textContent = text
      item.style.cssText = 'padding:6px 10px 3px;color:#78716c;font:10px system-ui,sans-serif;letter-spacing:.08em;text-transform:uppercase'
      return item
    }

    const pickRelation = (entry: SpawnRelation): void => {
      if (!current()) return
      const accepted = this.#spawnRelation({ defId: entry.defId, arity: entry.arity, invocation: snapshot })
      if (accepted === false) return
      this.#recents.note(entry.defId)
      if (current()) this.close()
    }

    const relationRow = (entry: SpawnRelation, fullId: boolean): HTMLElement => {
      const item = row(
        fullId ? entry.defId : entry.leaf,
        `${entry.namespace === null || fullId ? '' : `${entry.namespace} · `}/${entry.arity}`,
        () => pickRelation(entry),
      )
      item.dataset.defId = entry.defId
      return item
    }

    const binderLabel = (entry: SpawnBoundPredicateOption): string => entry.total === 1
      ? 'Bound predicate'
      : entry.position === 1
        ? 'Binder 1 (innermost)'
        : entry.position === entry.total
          ? `Binder ${entry.position} (outermost)`
          : `Binder ${entry.position}`

    const pickBoundPredicate = (entry: SpawnBoundPredicateOption): void => {
      if (!current()) return
      const accepted = this.#spawnBoundPredicate({ binder: entry.binder, invocation: snapshot })
      if (accepted === false) return
      if (current()) this.close()
    }

    const boundPredicateRow = (entry: SpawnBoundPredicateOption): HTMLElement => {
      const item = row(binderLabel(entry), `/${entry.arity}`, () => pickBoundPredicate(entry))
      item.classList.add('vpa-spawn-bound-predicate')
      item.dataset.binder = entry.binder
      const swatch = this.#document.createElement('span')
      swatch.className = 'vpa-spawn-binder-swatch'
      swatch.setAttribute('aria-hidden', 'true')
      swatch.style.cssText = `display:inline-block;width:9px;height:9px;margin-right:7px;border-radius:50%;background-color:${this.#binderColor(entry.binder)};box-shadow:0 0 0 1px #0002`
      item.firstElementChild?.prepend(swatch)
      item.addEventListener('pointerenter', () => {
        if (current()) this.#setHoveredBinder(entry.binder)
      })
      item.addEventListener('pointerleave', () => {
        if (current()) this.#setHoveredBinder(null)
      })
      return item
    }

    const showNamespace = (group: SpawnNamespaceGroup): void => {
      if (!current()) return
      submenu.replaceChildren(
        heading(group.label),
        ...group.entries.map((entry) => relationRow(entry, false)),
      )
      submenu.style.display = 'block'
    }

    const enterTermMode = (): void => {
      if (!current()) return
      termMode = true
      submenu.style.display = 'none'
      search.value = ''
      search.type = 'text'
      search.placeholder = 'λ-term, e.g. \\x. x x'
      search.setAttribute('aria-label', 'Lambda term to spawn')
      listing.replaceChildren(heading('Term'), row('Press Enter to place the term', '', null))
      search.focus()
    }

    const renderTree = (): void => {
      submenu.style.display = 'none'
      const nodes: HTMLElement[] = [row('λ term…', '', enterTermMode)]
      if (predicates.length > 0) {
        nodes.push(heading('Bound predicates'), ...predicates.map(boundPredicateRow))
      }
      const recent = this.#recents.list(catalog)
      if (recent.length > 0) nodes.push(heading('Recent'), ...recent.map((entry) => relationRow(entry, true)))
      if (catalog.groups.length > 0) nodes.push(heading('Namespaces'))
      for (const group of catalog.groups) {
        const groupRow = row(group.label, `${group.entries.length} ▸`, null)
        groupRow.style.cursor = 'pointer'
        groupRow.addEventListener('pointerenter', () => {
          groupRow.style.background = '#fef3c7'
          showNamespace(group)
        })
        groupRow.addEventListener('pointerleave', () => { groupRow.style.background = '#fff' })
        nodes.push(groupRow)
      }
      listing.replaceChildren(...nodes)
    }

    const renderSearch = (): void => {
      if (termMode || !current()) return
      const query = search.value.trim()
      if (query === '') {
        renderTree()
        return
      }
      submenu.style.display = 'none'
      const found = searchSpawnCatalog(catalog, query)
      const shown = found.slice(0, SEARCH_RESULT_LIMIT)
      const nodes = shown.map((entry) => relationRow(entry, true))
      if (found.length > shown.length) nodes.push(row(`…and ${found.length - shown.length} more`, '', null))
      if (nodes.length === 0) nodes.push(row('No relation matches', '', null))
      listing.replaceChildren(...nodes)
    }

    search.addEventListener('input', renderSearch)
    search.addEventListener('keydown', (event) => {
      event.stopPropagation()
      if (event.key === 'Escape') {
        event.preventDefault()
        this.escape()
        return
      }
      if (event.key !== 'Enter') return
      event.preventDefault()
      if (termMode) {
        if (search.value.trim() === '') return
        const accepted = this.#spawnTerm({ source: search.value, invocation: snapshot })
        if (accepted !== false && current()) this.close()
        return
      }
      const first = searchSpawnCatalog(catalog, search.value)[0]
      if (first !== undefined) pickRelation(first)
    })

    renderTree()
    queueMicrotask(() => { if (current()) search.focus() })
  }

  #setHoveredBinder(binder: RegionId | null): void {
    this.#hoverBinder?.(binder)
  }

  close(): boolean {
    this.#setHoveredBinder(null)
    if (this.#menu === null) return false
    this.#menu.remove()
    this.#backdrop?.remove()
    this.#menu = null
    this.#backdrop = null
    this.#invocation = null
    this.#openChanged?.(false)
    return true
  }

  escape(): boolean {
    return this.close()
  }

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
