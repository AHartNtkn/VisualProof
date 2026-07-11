import type { LibraryRenderer, LibraryViewActions, LibraryViewState } from '../src/app'
import type { DiagramWithBoundary } from '../src/kernel/diagram/boundary'
import type { Theorem } from '../src/kernel/proof/theorem'
import { fitCamera } from '../src/view/camera'
import { drawShapes } from '../src/view/canvas'
import { mkEngine } from '../src/view/engine'
import { paint } from '../src/view/paint'
import { seedProject, settle } from '../src/view/relax'

export type LibraryPrototypeVariant = 'ledger' | 'prism' | 'shelf'

type KnowledgeItem = {
  readonly key: string
  readonly kind: 'relation' | 'theorem'
  readonly name: string
  readonly source: string
  readonly relation?: DiagramWithBoundary
  readonly theorem?: Theorem
}

type RenderContext = {
  readonly host: HTMLElement
  readonly state: LibraryViewState
  readonly actions: LibraryViewActions
}

function itemsOf(state: LibraryViewState): KnowledgeItem[] {
  const out: KnowledgeItem[] = []
  for (const entry of state.library.entries) {
    if (entry.status !== 'loaded') continue
    for (const [name, relation] of Object.entries(entry.theory.relations)) {
      out.push({ key: `${entry.file}:relation:${name}`, kind: 'relation', name, source: entry.file, relation })
    }
    for (const theorem of entry.theory.theorems) {
      out.push({ key: `${entry.file}:theorem:${theorem.name}`, kind: 'theorem', name: theorem.name, source: entry.file, theorem })
    }
  }
  for (const { name, relation } of state.library.definedRelations) {
    out.push({ key: `Session:relation:${name}`, kind: 'relation', name, source: 'Session', relation })
  }
  for (const theorem of state.library.adopted) {
    out.push({ key: `Session:theorem:${theorem.name}`, kind: 'theorem', name: theorem.name, source: 'Session', theorem })
  }
  return out.sort((a, b) => a.name.localeCompare(b.name) || a.kind.localeCompare(b.kind) || a.source.localeCompare(b.source))
}

function preview(doc: Document, dwb: DiagramWithBoundary, state: LibraryViewState, label: string): HTMLCanvasElement {
  const canvas = doc.createElement('canvas')
  canvas.className = 'lib-preview'
  canvas.width = 300
  canvas.height = 150
  canvas.setAttribute('role', 'img')
  canvas.setAttribute('aria-label', label)
  const context = canvas.getContext('2d')
  if (context === null) throw new Error('the Library preview canvas has no 2d context')
  const engine = mkEngine(dwb.diagram, dwb.boundary)
  seedProject(engine)
  settle(engine, 180)
  const frame = engine.frame === null ? undefined : { center: engine.frame.center, radius: engine.frame.half }
  const view = fitCamera(frame, canvas.width, canvas.height, 1)
  context.fillStyle = state.theme.canvas
  context.fillRect(0, 0, canvas.width, canvas.height)
  drawShapes(context, paint(engine, state.theme), view)
  return canvas
}

const textButton = (doc: Document, label: string, className = ''): HTMLButtonElement => {
  const button = doc.createElement('button')
  button.type = 'button'
  button.textContent = label
  button.className = className
  return button
}

export function createLibraryPrototype(variant: LibraryPrototypeVariant): LibraryRenderer {
  let projection: 'browse' | 'sources' = 'browse'
  let browseQuery = ''
  let sourceQuery = ''
  let kind: 'all' | 'relation' | 'theorem' = 'all'
  let source = 'all'
  let inspected: string | null = null
  let last: RenderContext | null = null

  const refresh = (): void => {
    if (last !== null) draw(last)
  }

  const focusItem = (key: string): void => {
    const rows = last?.host.querySelectorAll<HTMLButtonElement>('.lib-item-row') ?? []
    ;[...rows].find((row) => row.dataset.itemKey === key)?.focus()
  }

  const drawInspector = (root: HTMLElement, item: KnowledgeItem, context: RenderContext): void => {
    const doc = root.ownerDocument
    root.classList.add('is-inspecting')
    const back = textButton(doc, '‹ Results', 'lib-back')
    back.addEventListener('click', () => {
      inspected = null
      refresh()
      focusItem(item.key)
    })
    root.append(back)

    const heading = doc.createElement('div')
    heading.className = 'lib-inspector-heading'
    heading.innerHTML = `<span>${item.kind === 'relation' ? 'REL' : 'THM'}</span><h3>${item.name}</h3><small>${item.source}</small>`
    root.append(heading)

    if (item.kind === 'relation' && item.relation !== undefined) {
      const facts = doc.createElement('p')
      facts.className = 'lib-inspector-facts'
      facts.textContent = `${item.relation.boundary.length} ${item.relation.boundary.length === 1 ? 'port' : 'ports'} · port 0 is the prominent boundary dot`
      root.append(facts, preview(doc, item.relation, context.state, `Definition of relation ${item.name}`))
      const note = doc.createElement('p')
      note.className = 'lib-inspector-note'
      note.textContent = 'Available from the contextual relation browser on the diagram.'
      root.append(note)
    }

    if (item.kind === 'theorem' && item.theorem !== undefined) {
      const facts = doc.createElement('p')
      facts.className = 'lib-inspector-facts'
      const totalSteps = item.theorem.steps.length + (item.theorem.backSteps?.length ?? 0)
      facts.textContent = `Verified · ${totalSteps} ${totalSteps === 1 ? 'step' : 'steps'}`
      const lhs = doc.createElement('section')
      lhs.className = 'lib-statement-side'
      lhs.append('LEFT', preview(doc, item.theorem.lhs, context.state, `Left side of theorem ${item.name}`))
      const rhs = doc.createElement('section')
      rhs.className = 'lib-statement-side'
      rhs.append('RIGHT', preview(doc, item.theorem.rhs, context.state, `Right side of theorem ${item.name}`))
      const replay = textButton(doc, 'Replay proof', 'lib-replay')
      replay.addEventListener('click', () => context.actions.replay(item.name))
      root.append(facts, lhs, rhs, replay)
    }
  }

  const drawBrowse = (root: HTMLElement, context: RenderContext): void => {
    const doc = root.ownerDocument
    const allItems = itemsOf(context.state)
    const sources = [...new Set(allItems.map((item) => item.source))].sort((a, b) => a.localeCompare(b))

    if (variant === 'shelf') {
      const shelf = doc.createElement('div')
      shelf.className = 'lib-source-shelf'
      const labels = ['all', ...sources]
      for (const label of labels) {
        const control = textButton(doc, label === 'all' ? 'All knowledge' : label)
        control.classList.toggle('is-active', source === label)
        control.addEventListener('click', () => { source = label; inspected = null; refresh() })
        shelf.append(control)
      }
      const manage = textButton(doc, 'Manage…', 'lib-manage')
      manage.addEventListener('click', () => { projection = 'sources'; inspected = null; refresh() })
      shelf.append(manage)
      root.append(shelf)
    }

    const search = doc.createElement('input')
    search.type = 'search'
    search.className = 'lib-search'
    search.placeholder = 'Search verified knowledge'
    search.value = browseQuery
    search.setAttribute('aria-label', 'Search verified knowledge')
    search.addEventListener('input', () => { browseQuery = search.value; inspected = null; refresh() })
    root.append(search)

    const filters = doc.createElement('div')
    filters.className = 'lib-filters'
    for (const option of ['all', 'relation', 'theorem'] as const) {
      const control = textButton(doc, option === 'all' ? 'All' : option === 'relation' ? 'Relations' : 'Theorems')
      control.classList.toggle('is-active', kind === option)
      control.addEventListener('click', () => { kind = option; inspected = null; refresh() })
      filters.append(control)
    }
    if (variant !== 'shelf') {
      const select = doc.createElement('select')
      select.className = 'lib-source-filter'
      select.setAttribute('aria-label', 'Filter by source')
      for (const label of ['all', ...sources]) {
        const option = doc.createElement('option')
        option.value = label
        option.textContent = label === 'all' ? 'All sources' : label
        option.selected = source === label
        select.append(option)
      }
      select.addEventListener('change', () => { source = select.value; inspected = null; refresh() })
      filters.append(select)
    }
    root.append(filters)

    const normalized = browseQuery.trim().toLocaleLowerCase()
    const shown = allItems.filter((item) =>
      (kind === 'all' || item.kind === kind)
      && (source === 'all' || item.source === source)
      && (normalized === '' || `${item.name} ${item.source} ${item.kind}`.toLocaleLowerCase().includes(normalized)),
    )
    const count = doc.createElement('p')
    count.className = 'lib-result-count'
    count.textContent = `${shown.length} of ${allItems.length} verified items`
    root.append(count)

    const list = doc.createElement('div')
    list.className = 'lib-results'
    list.setAttribute('role', 'listbox')
    for (const item of shown) {
      const row = textButton(doc, '', 'lib-item-row')
      row.dataset.itemKey = item.key
      row.dataset.itemKind = item.kind
      row.dataset.itemName = item.name
      row.setAttribute('role', 'option')
      const detail = item.kind === 'relation'
        ? `${item.relation?.boundary.length ?? 0} ports`
        : `${(item.theorem?.steps.length ?? 0) + (item.theorem?.backSteps?.length ?? 0)} steps`
      row.innerHTML = `<span class="lib-kind">${item.kind === 'relation' ? 'REL' : 'THM'}</span><b>${item.name}</b><small>${detail} · ${item.source}</small>`
      row.addEventListener('click', () => {
        inspected = item.key
        refresh()
        last?.host.querySelector<HTMLButtonElement>('.lib-back')?.focus()
      })
      list.append(row)
    }
    if (shown.length === 0) {
      const empty = doc.createElement('p')
      empty.className = 'lib-empty'
      empty.textContent = 'No verified knowledge matches these filters.'
      list.append(empty)
    }
    list.addEventListener('keydown', (event) => {
      if (event.key !== 'ArrowDown' && event.key !== 'ArrowUp' && event.key !== 'Home' && event.key !== 'End') return
      const rows = [...list.querySelectorAll<HTMLButtonElement>('.lib-item-row')]
      if (rows.length === 0) return
      const current = rows.indexOf(doc.activeElement as HTMLButtonElement)
      const next = event.key === 'Home' ? 0
        : event.key === 'End' ? rows.length - 1
          : event.key === 'ArrowDown' ? Math.min(rows.length - 1, Math.max(0, current + 1))
            : Math.max(0, current < 0 ? 0 : current - 1)
      rows[next]?.focus()
      event.preventDefault()
    })
    root.append(list)

    if (inspected !== null) {
      const item = allItems.find((candidate) => candidate.key === inspected)
      if (item === undefined) inspected = null
      else {
        root.replaceChildren()
        drawInspector(root, item, context)
      }
    }
  }

  const drawSources = (root: HTMLElement, context: RenderContext): void => {
    const doc = root.ownerDocument
    const actions = doc.createElement('div')
    actions.className = 'lib-source-tools'
    const folder = textButton(doc, 'Open folder…')
    folder.addEventListener('click', context.actions.openFolder)
    const file = textButton(doc, 'Open file…')
    file.addEventListener('click', context.actions.openFile)
    const rescan = textButton(doc, 'Rescan folder')
    rescan.disabled = context.state.folderName === null
    rescan.addEventListener('click', context.actions.rescanFolder)
    actions.append(folder, file, rescan)
    root.append(actions)

    const workspace = doc.createElement('p')
    workspace.className = 'lib-workspace'
    workspace.textContent = context.state.folderName === null ? 'No workspace folder open' : `Workspace · ${context.state.folderName}`
    root.append(workspace)

    const list = doc.createElement('div')
    list.className = 'lib-source-list'
    const queryLower = sourceQuery.trim().toLowerCase()
    for (const entry of context.state.library.entries) {
      if (queryLower !== '' && !entry.file.toLowerCase().includes(queryLower)) continue
      const row = doc.createElement('section')
      row.className = 'lib-source-row'
      row.dataset.sourceFile = entry.file
      const error = context.state.errors.get(entry.file)
      const counts = entry.status === 'loaded'
        ? `${Object.keys(entry.theory.relations).length} REL · ${entry.theory.theorems.length} THM`
        : ''
      const stateLabel = error !== undefined ? 'Load failed' : entry.status === 'loaded' ? 'Loaded' : 'Available'
      row.innerHTML = `<div class="lib-source-name"><b>${entry.file}</b><span>${stateLabel}</span><small>${counts}</small></div>`
      const lifecycle = textButton(doc, error !== undefined ? 'Retry' : entry.status === 'loaded' ? 'Unload' : 'Load', 'lib-source-action')
      lifecycle.addEventListener('click', () => entry.status === 'loaded' ? context.actions.unload(entry.file) : context.actions.load(entry.file))
      row.append(lifecycle)
      if (error !== undefined) {
        const diagnostic = doc.createElement('p')
        diagnostic.className = 'lib-source-error'
        diagnostic.textContent = error
        row.append(diagnostic)
      }
      list.append(row)
    }

    const session = doc.createElement('section')
    session.className = 'lib-source-row'
    session.dataset.sourceFile = 'Session'
    session.innerHTML = `<div class="lib-source-name"><b>Session</b><span>Live</span><small>${context.state.library.definedRelations.length} REL · ${context.state.library.adopted.length} THM</small></div>`
    list.append(session)
    root.append(list)
  }

  const draw = (context: RenderContext): void => {
    last = context
    const { host } = context
    const doc = host.ownerDocument
    host.replaceChildren()
    host.className = 'lib-prototype'
    host.dataset.libraryVariant = variant

    const root = doc.createElement('div')
    root.className = 'lib-prototype-body'

    if (variant === 'ledger') {
      const tabs = doc.createElement('div')
      tabs.className = 'lib-mode-tabs'
      for (const mode of ['browse', 'sources'] as const) {
        const control = textButton(doc, mode === 'browse' ? 'Browse' : `Sources${context.state.errors.size > 0 ? ` · ${context.state.errors.size}` : ''}`)
        control.classList.toggle('is-active', projection === mode)
        control.addEventListener('click', () => { projection = mode; inspected = null; refresh() })
        tabs.append(control)
      }
      root.append(tabs)
    } else if (variant === 'prism') {
      const route = textButton(doc,
        projection === 'browse'
          ? `Sources${context.state.errors.size > 0 ? ` · ${context.state.errors.size} needs attention` : ''} ›`
          : '‹ Verified knowledge',
        'lib-projection-route',
      )
      route.addEventListener('click', () => { projection = projection === 'browse' ? 'sources' : 'browse'; inspected = null; refresh() })
      root.append(route)
    } else if (projection === 'sources') {
      const back = textButton(doc, '‹ Knowledge shelf', 'lib-projection-route')
      back.addEventListener('click', () => { projection = 'browse'; inspected = null; refresh() })
      root.append(back)
    }

    if (projection === 'browse') drawBrowse(root, context)
    else {
      const sourceSearch = doc.createElement('input')
      sourceSearch.type = 'search'
      sourceSearch.className = 'lib-search'
      sourceSearch.placeholder = 'Search sources'
      sourceSearch.value = sourceQuery
      sourceSearch.setAttribute('aria-label', 'Search sources')
      sourceSearch.addEventListener('input', () => { sourceQuery = sourceSearch.value; refresh() })
      root.append(sourceSearch)
      drawSources(root, context)
    }

    host.append(root)
    host.onkeydown = (event) => {
      const target = event.target as HTMLElement | null
      const isEditing = target?.matches?.('input, textarea, select, [contenteditable="true"]') ?? false
      if (event.key === '/' && !isEditing) {
        root.querySelector<HTMLInputElement>('.lib-search')?.focus()
        event.preventDefault()
      } else if (event.key === 'Escape') {
        if (inspected !== null) {
          const key = inspected
          inspected = null
          refresh()
          focusItem(key)
        } else if (projection === 'browse' && browseQuery !== '') {
          browseQuery = ''
          refresh()
          last?.host.querySelector<HTMLInputElement>('.lib-search')?.focus()
        } else if (projection === 'sources' && sourceQuery !== '') {
          sourceQuery = ''
          refresh()
          last?.host.querySelector<HTMLInputElement>('.lib-search')?.focus()
        } else {
          host.dispatchEvent(new CustomEvent('vpa-library-close', { bubbles: true }))
        }
        event.preventDefault()
      }
    }
  }

  return (host, state, actions) => draw({ host, state, actions })
}
