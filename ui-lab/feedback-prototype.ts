import type { FeedbackAnchor, FeedbackNotice, FeedbackState } from '../src/app'

export type FeedbackPrototypeVariant = 'field' | 'ribbon' | 'chronicle'

type DebugApi = {
  feedback(): FeedbackState
  replay(): { mode: string; k: number; n: number; label: string }
  view(): { scale: number; offsetX: number; offsetY: number }
  bodies(): { id: string; x: number; y: number; r: number }[]
  regions(): { id: string; x: number; y: number; r: number }[]
  wires(): { id: string; x: number; y: number }[]
}

type DemoWindow = Window & { __vpaDebug?: DebugApi }
type Placement = { readonly x: number; readonly y: number; readonly width: number; readonly height: number }
type ChronicleEntry = { readonly notice: FeedbackNotice; readonly arrived: number }

const center = (placement: Placement): { x: number; y: number } => ({
  x: placement.x + placement.width / 2,
  y: placement.y + placement.height / 2,
})

const average = (placements: readonly Placement[]): Placement | null => {
  if (placements.length === 0) return null
  const points = placements.map(center)
  const x = points.reduce((sum, point) => sum + point.x, 0) / points.length
  const y = points.reduce((sum, point) => sum + point.y, 0) / points.length
  const minX = Math.min(...placements.map((placement) => placement.x))
  const minY = Math.min(...placements.map((placement) => placement.y))
  const maxX = Math.max(...placements.map((placement) => placement.x + placement.width))
  const maxY = Math.max(...placements.map((placement) => placement.y + placement.height))
  return { x: Math.min(x, minX), y: Math.min(y, minY), width: Math.max(18, maxX - minX), height: Math.max(18, maxY - minY) }
}

function innerControlPlacement(frame: HTMLIFrameElement, id: string): Placement | null {
  const frameBounds = frame.getBoundingClientRect()
  const doc = frame.contentDocument
  if (doc === null) return null
  const direct = doc.getElementById(id)
  const fallback = id === 'save'
    ? [...doc.querySelectorAll<HTMLButtonElement>('button')].find((button) => button.textContent?.startsWith('Save theory'))
    : id === 'theorem-name' ? doc.getElementById('theorem-name')
      : id === 'action-menu' ? doc.getElementById('action-menu')
        : null
  const element = direct ?? fallback
  if (!(element instanceof frame.contentWindow!.HTMLElement)) return null
  const rect = element.getBoundingClientRect()
  if (rect.width === 0 || rect.height === 0) return null
  return { x: frameBounds.x + rect.x, y: frameBounds.y + rect.y, width: rect.width, height: rect.height }
}

function controlPlacement(host: HTMLElement, frame: HTMLIFrameElement, id: string): Placement | null {
  const selector = id === 'mode' || id === 'lifecycle' ? '.layout-mode'
    : id === 'history' ? '.layout-temporal'
      : id === 'library' ? '.layout-library-button'
        : null
  const element = selector === null ? null : host.querySelector<HTMLElement>(selector)
  if (element !== null && !element.hidden) {
    const rect = element.getBoundingClientRect()
    return { x: rect.x, y: rect.y, width: rect.width, height: rect.height }
  }
  return innerControlPlacement(frame, id)
}

function placeAnchor(host: HTMLElement, frame: HTMLIFrameElement, debug: DebugApi, anchor: FeedbackAnchor): Placement {
  const frameBounds = frame.getBoundingClientRect()
  const view = debug.view()
  const world = (x: number, y: number, radius = 6): Placement => ({
    x: frameBounds.x + x * view.scale + view.offsetX - radius * view.scale,
    y: frameBounds.y + y * view.scale + view.offsetY - radius * view.scale,
    width: Math.max(12, radius * view.scale * 2),
    height: Math.max(12, radius * view.scale * 2),
  })
  const hit = (kind: 'node' | 'region' | 'wire', id: string): Placement | null => {
    if (kind === 'node') {
      const body = debug.bodies().find((candidate) => candidate.id === id)
      return body === undefined ? null : world(body.x, body.y, body.r)
    }
    if (kind === 'region') {
      const region = debug.regions().find((candidate) => candidate.id === id)
      return region === undefined ? null : world(region.x, region.y, region.r)
    }
    const wire = debug.wires().find((candidate) => candidate.id === id)
    return wire === undefined ? null : world(wire.x, wire.y, 3 / view.scale)
  }
  if (anchor.kind === 'node') return hit('node', anchor.id) ?? { x: frameBounds.x + frameBounds.width / 2, y: frameBounds.y + frameBounds.height / 2, width: 1, height: 1 }
  if (anchor.kind === 'hit') return hit(anchor.hit.kind, anchor.hit.id) ?? placeAnchor(host, frame, debug, { kind: 'viewport' })
  if (anchor.kind === 'selection') {
    return average(anchor.hits.flatMap((item) => {
      const placement = hit(item.kind, item.id)
      return placement === null ? [] : [placement]
    })) ?? placeAnchor(host, frame, debug, { kind: 'viewport' })
  }
  if (anchor.kind === 'point') return world(anchor.point.x, anchor.point.y, 4 / view.scale)
  if (anchor.kind === 'control') return controlPlacement(host, frame, anchor.id) ?? placeAnchor(host, frame, debug, { kind: 'viewport' })
  return { x: frameBounds.x + frameBounds.width / 2 - 1, y: frameBounds.y + frameBounds.height / 2 - 1, width: 2, height: 2 }
}

const transientLifetime = (notice: FeedbackNotice): number => notice.kind === 'refusal'
  ? Math.min(10_000, Math.max(4_000, notice.text.length * 42))
  : notice.kind === 'success' ? 2_000 : 3_200

export function installFeedbackPrototype(host: HTMLElement, frame: HTMLIFrameElement, variant: FeedbackPrototypeVariant): () => void {
  const win = frame.contentWindow as DemoWindow | null
  if (win?.__vpaDebug === undefined) throw new Error('the real feedback authority is unavailable')
  const debug = win.__vpaDebug
  const layer = document.createElement('section')
  layer.className = 'feedback-layer'
  layer.dataset.feedbackVariant = variant
  layer.setAttribute('aria-label', 'Application feedback')

  const guide = document.createElement('aside')
  guide.className = 'feedback-demo-guide'
  guide.innerHTML = '<b>TRY THE REAL APP</b><span>Ctrl-drag a node · release Ctrl before pointer-up to pin</span><span>Select, then Shift+W · enter invalid arity for a persistent field problem</span><span>Right-click · enter an invalid λ-term for a verbatim refusal</span>'
  const callout = document.createElement('output')
  callout.className = 'feedback-callout'
  callout.hidden = true
  const pulse = document.createElement('span')
  pulse.className = 'feedback-pulse'
  pulse.hidden = true
  const issues = document.createElement('div')
  issues.className = 'feedback-issues'
  issues.hidden = true
  const chronicle = document.createElement('aside')
  chronicle.className = 'feedback-chronicle'
  chronicle.hidden = variant !== 'chronicle'
  const polite = document.createElement('span')
  polite.className = 'feedback-sr'
  polite.setAttribute('role', 'status')
  polite.setAttribute('aria-live', 'polite')
  const assertive = document.createElement('span')
  assertive.className = 'feedback-sr'
  assertive.setAttribute('role', 'alert')
  layer.append(guide, pulse, callout, issues, chronicle, polite, assertive)
  host.append(layer)

  let raf = 0
  let currentSequence = 0
  let currentUntil = 0
  let chronicleEntries: ChronicleEntry[] = []
  let issuesOpen = false
  let problemSignature = ''
  let chronicleSignature = ''

  const renderIssues = (state: FeedbackState): void => {
    if (state.problems.length === 0 || variant === 'chronicle') {
      issues.hidden = true
      issues.replaceChildren()
      return
    }
    issues.hidden = false
    const button = document.createElement('button')
    button.type = 'button'
    button.className = 'feedback-issue-button'
    button.textContent = `${state.problems.length} unresolved ${state.problems.length === 1 ? 'issue' : 'issues'}`
    button.setAttribute('aria-expanded', String(issuesOpen))
    button.addEventListener('click', () => {
      issuesOpen = !issuesOpen
      renderIssues(state)
    })
    issues.replaceChildren(button)
    if (issuesOpen) {
      const list = document.createElement('div')
      list.className = 'feedback-issue-list'
      for (const problem of state.problems) {
        const row = document.createElement('p')
        row.textContent = problem.text
        list.append(row)
      }
      issues.append(list)
    }
  }

  const renderChronicle = (state: FeedbackState): void => {
    if (variant !== 'chronicle') return
    const signature = `${state.problems.map((notice) => notice.sequence).join(',')}|${chronicleEntries.map((entry) => entry.notice.sequence).join(',')}`
    if (signature === chronicleSignature) return
    chronicleSignature = signature
    const title = document.createElement('header')
    title.innerHTML = '<b>CHRONICLE</b><span>Recent authoritative signals</span>'
    const problemRows = state.problems.map((notice) => {
      const row = document.createElement('div')
      row.className = 'feedback-chronicle-row is-problem'
      row.innerHTML = `<small>UNRESOLVED</small><span>${notice.text}</span>`
      return row
    })
    const eventRows = chronicleEntries.map(({ notice }) => {
      const row = document.createElement('div')
      row.className = 'feedback-chronicle-row'
      row.dataset.kind = notice.kind
      row.innerHTML = `<small>${notice.kind.toUpperCase()}</small><span>${notice.text}</span>`
      return row
    })
    const empty = document.createElement('p')
    empty.className = 'feedback-chronicle-empty'
    empty.textContent = 'Completed actions collect here. Active guidance and refusals stay with the diagram.'
    chronicle.replaceChildren(title, ...problemRows, ...eventRows, ...(problemRows.length + eventRows.length === 0 ? [empty] : []))
  }

  const synchronize = (): void => {
    const state = debug.feedback()
    const notice = state.current
    const now = performance.now()
    if (notice !== null && notice.sequence !== currentSequence) {
      currentSequence = notice.sequence
      currentUntil = now + transientLifetime(notice)
      if (notice.kind === 'refusal' || notice.kind === 'problem') assertive.textContent = notice.text
      else polite.textContent = notice.text
      if (variant === 'chronicle' && notice.kind !== 'guidance' && notice.kind !== 'refusal' && notice.kind !== 'ambient' && notice.persistence !== 'problem') {
        chronicleEntries = [{ notice, arrived: now }, ...chronicleEntries].slice(0, 6)
      }
      renderChronicle(state)
    }

    const nextProblemSignature = state.problems.map((problem) => problem.sequence).join(',')
    if (nextProblemSignature !== problemSignature) {
      problemSignature = nextProblemSignature
      renderIssues(state)
      renderChronicle(state)
    }

    const placement = notice === null ? null : placeAnchor(host, frame, debug, notice.owner)
    const persistent = notice?.persistence === 'state' || notice?.persistence === 'interaction' || notice?.persistence === 'problem'
    const visible = notice !== null && (persistent || now < currentUntil)
    const visibleText = visible && (variant === 'ribbon'
      || notice?.kind === 'guidance'
      || notice?.kind === 'refusal'
      || notice?.kind === 'problem'
      || notice?.kind === 'ambient'
      || (notice?.kind === 'success' && (notice.affected?.length ?? 0) === 0))
    callout.hidden = !visibleText
    const selfEvidentFieldSuccess = variant === 'field'
      && notice?.kind === 'success'
      && (notice.affected?.length ?? 0) > 0
    pulse.hidden = !(visible && placement !== null && notice?.kind !== 'ambient' && !selfEvidentFieldSuccess)
    if (visible && placement !== null && notice !== null) {
      callout.dataset.kind = notice.kind
      callout.textContent = notice.text
      const point = center(placement)
      const calloutWidth = Math.min(330, Math.max(190, notice.text.length * 5.2))
      const left = Math.max(12, Math.min(window.innerWidth - calloutWidth - 12, point.x + 16))
      const top = Math.max(58, Math.min(window.innerHeight - 92, point.y - 22))
      callout.style.left = `${left}px`
      callout.style.top = `${top}px`
      pulse.style.left = `${placement.x}px`
      pulse.style.top = `${placement.y}px`
      pulse.style.width = `${placement.width}px`
      pulse.style.height = `${placement.height}px`
    }
    if (variant === 'chronicle') {
      const retained = chronicleEntries.filter((entry) => now - entry.arrived < 14_000)
      if (retained.length !== chronicleEntries.length) {
        chronicleEntries = retained
        renderChronicle(state)
      }
    }
    raf = requestAnimationFrame(synchronize)
  }
  synchronize()
  return () => {
    cancelAnimationFrame(raf)
    layer.remove()
  }
}
