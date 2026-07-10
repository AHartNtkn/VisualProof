export type LayoutVariant = 'compass' | 'bookmark' | 'workbench'
export type AestheticVariant = 'carbon' | 'basalt' | 'porcelain'

type DebugApi = {
  status(): string
  replay(): { mode: string; k: number; n: number; label: string }
}

type AppWindow = Window & { __vpaDebug?: DebugApi }

const button = (label: string, className = ''): HTMLButtonElement => {
  const element = document.createElement('button')
  element.type = 'button'
  element.textContent = label
  element.className = className
  return element
}

const findButton = (doc: Document, startsWith: string): HTMLButtonElement | null =>
  [...doc.querySelectorAll<HTMLButtonElement>('button')].find((candidate) =>
    candidate.textContent?.trim().startsWith(startsWith),
  ) ?? null

const waitForApp = async (frame: HTMLIFrameElement): Promise<{ win: AppWindow; doc: Document }> => {
  await new Promise<void>((resolve, reject) => {
    const finish = (): void => resolve()
    frame.addEventListener('load', finish, { once: true })
    frame.addEventListener('error', () => reject(new Error('the application frame failed to load')), { once: true })
  })

  const win = frame.contentWindow as AppWindow | null
  const doc = frame.contentDocument
  if (win === null || doc === null) throw new Error('the application frame is not same-origin')

  const deadline = performance.now() + 10_000
  while (win.__vpaDebug === undefined) {
    if (performance.now() > deadline) throw new Error('the real application did not expose its debug seam')
    await new Promise((resolve) => window.setTimeout(resolve, 25))
  }
  return { win, doc }
}

export const mountLayoutFrame = async (
  host: HTMLElement,
  variant: LayoutVariant,
  aesthetic?: AestheticVariant,
  appSource?: string,
): Promise<void> => {
  host.className = 'layout-lab'
  host.dataset.variant = variant
  if (aesthetic !== undefined) host.dataset.aesthetic = aesthetic
  host.dataset.ready = 'false'

  const stage = document.createElement('main')
  stage.className = 'layout-stage'

  const frame = document.createElement('iframe')
  frame.className = 'layout-app'
  frame.title = 'Real Visual Proof Assistant'
  frame.src = appSource ?? (aesthetic === undefined
    ? '/app/index.html?debug'
    : `/ui-lab/aesthetic-app.html?debug&aesthetic=${aesthetic}`)
  stage.append(frame)

  const north = document.createElement('header')
  north.className = 'layout-north'
  north.setAttribute('aria-label', 'Proof lifecycle')

  const identity = document.createElement('div')
  identity.className = 'layout-identity'
  identity.innerHTML = '<span class="layout-mark" aria-hidden="true">VPA</span><span class="layout-document">Proof workspace</span>'

  const trail = document.createElement('div')
  trail.className = 'layout-trail'
  const editStep = button('EDIT', 'layout-trail-step is-current')
  const proveStep = button('PROVE', 'layout-trail-step')
  const replayStep = button('REPLAY', 'layout-trail-step')
  trail.append(editStep, proveStep, replayStep)

  const modeButton = button('EDIT', 'layout-mode')
  modeButton.setAttribute('aria-expanded', 'false')

  const lifecycle = document.createElement('section')
  lifecycle.className = 'layout-popover layout-lifecycle'
  lifecycle.hidden = true
  lifecycle.innerHTML = '<p class="layout-kicker">Proof lifecycle</p><p class="layout-help">Use the current sheet as either side of a fixed statement, then enter proving.</p>'
  const lifecycleActions = document.createElement('div')
  lifecycleActions.className = 'layout-action-row'
  const setLhs = button('Use as left side')
  const setRhs = button('Use as right side')
  const toggleMode = button('Enter proving', 'is-primary')
  lifecycleActions.append(setLhs, setRhs, toggleMode)
  lifecycle.append(lifecycleActions)

  const utilitiesButton = button('•••', 'layout-utilities-button')
  utilitiesButton.title = 'View and session utilities'
  utilitiesButton.setAttribute('aria-expanded', 'false')
  const utilities = document.createElement('section')
  utilities.className = 'layout-popover layout-utilities'
  utilities.hidden = true
  utilities.innerHTML = '<p class="layout-kicker">View & session</p>'
  const theme = button('Theme')
  const companion = button('Companion view')
  const undo = button('Undo')
  utilities.append(theme, companion, undo)
  const workflowKicker = document.createElement('p')
  workflowKicker.className = 'layout-kicker layout-workflow-kicker'
  workflowKicker.textContent = 'Real workflow references'
  const dualLink = document.createElement('a')
  dualLink.href = '/ui-lab/round12-b.html'
  dualLink.textContent = 'Dual-front proving ↗'
  const formulaLink = document.createElement('a')
  formulaLink.href = '/ui-lab/round13-a.html?debug'
  formulaLink.textContent = 'Formula editor ↗'
  utilities.append(workflowKicker, dualLink, formulaLink)

  north.append(identity, trail, modeButton, utilitiesButton, lifecycle, utilities)

  const libraryButton = button('Library', 'layout-library-button')
  libraryButton.setAttribute('aria-expanded', 'false')
  const librarySurface = document.createElement('aside')
  librarySurface.className = 'layout-library'
  librarySurface.setAttribute('aria-label', 'Library')
  librarySurface.hidden = true
  const libraryHead = document.createElement('div')
  libraryHead.className = 'layout-surface-head'
  libraryHead.innerHTML = '<span><b>Library</b><small>Theories, relations, and saved proofs</small></span>'
  const closeLibrary = button('×', 'layout-close')
  closeLibrary.title = 'Close library'
  libraryHead.append(closeLibrary)
  const libraryBody = document.createElement('div')
  libraryBody.className = 'layout-library-body'
  librarySurface.append(libraryHead, libraryBody)

  const temporal = document.createElement('footer')
  temporal.className = 'layout-temporal'
  temporal.hidden = true
  temporal.innerHTML = '<button type="button" class="layout-undo" title="Previous">↶</button><input class="layout-time-range" type="range" min="0" max="0" value="0" disabled aria-label="History position"><span class="layout-time-label">Current state</span><button type="button" class="layout-redo" title="Next">↷</button>'

  const demoSwitch = document.createElement('nav')
  demoSwitch.className = 'layout-demo-switch'
  demoSwitch.setAttribute('aria-label', aesthetic === undefined ? 'Compare layout variants' : 'Compare aesthetic variants')
  demoSwitch.innerHTML = aesthetic === undefined
    ? '<span>COMPARE</span><a href="/ui-lab/round14-a.html" data-variant-link="compass">A</a><a href="/ui-lab/round14-b.html" data-variant-link="bookmark">B</a><a href="/ui-lab/round14-c.html" data-variant-link="workbench">C</a>'
    : '<span>COMPARE</span><a href="/ui-lab/round15-a.html" data-aesthetic-link="carbon">A</a><a href="/ui-lab/round15-b.html" data-aesthetic-link="basalt">B</a><a href="/ui-lab/round15-c.html" data-aesthetic-link="porcelain">C</a>'

  host.append(stage, north, libraryButton, librarySurface, temporal, demoSwitch)

  const currentLink = aesthetic === undefined
    ? demoSwitch.querySelector<HTMLAnchorElement>(`[data-variant-link="${variant}"]`)
    : demoSwitch.querySelector<HTMLAnchorElement>(`[data-aesthetic-link="${aesthetic}"]`)
  currentLink?.classList.add('is-current')

  const setOpen = (surface: 'library' | 'lifecycle' | 'utilities', open: boolean): void => {
    const target = surface === 'library' ? librarySurface : surface === 'lifecycle' ? lifecycle : utilities
    const trigger = surface === 'library' ? libraryButton : surface === 'lifecycle' ? modeButton : utilitiesButton
    target.hidden = !open
    trigger.setAttribute('aria-expanded', String(open))
    host.classList.toggle(`has-${surface}`, open)
  }

  libraryButton.addEventListener('click', () => setOpen('library', librarySurface.hidden))
  closeLibrary.addEventListener('click', () => setOpen('library', false))
  librarySurface.addEventListener('vpa-library-close', () => {
    setOpen('library', false)
    libraryButton.focus()
  })
  librarySurface.addEventListener('vpa-library-replay', () => setOpen('library', false))
  modeButton.addEventListener('click', () => setOpen('lifecycle', lifecycle.hidden))
  utilitiesButton.addEventListener('click', () => setOpen('utilities', utilities.hidden))

  const { win, doc } = await waitForApp(frame)
  const chrome = doc.getElementById('chrome')
  const actualLibrary = doc.getElementById('library')
  const actualMenu = doc.getElementById('action-menu')
  if (chrome === null || actualLibrary === null || actualMenu === null) {
    throw new Error('the real application shell is missing its authoritative surfaces')
  }

  const appStyle = doc.createElement('style')
  appStyle.dataset.layoutFrame = 'true'
  appStyle.textContent = `
    #chrome { display: contents !important; }
    #chrome > .vpa-row, #chrome > .vpa-status { display: none !important; }
    #action-menu[hidden], #action-menu:empty { display: none !important; }
    #action-menu:not([hidden]):not(:empty) {
      display: flex !important; gap: 5px !important; flex-wrap: wrap;
      max-width: min(720px, calc(100vw - 32px)); padding: 6px !important;
      border: 1px solid #948b7c; border-radius: 999px; background: rgba(255,255,252,.96); color: #282621;
      box-shadow: 0 8px 28px rgba(48,42,33,.16); pointer-events: auto !important;
    }
    #action-menu button { border: 0; border-radius: 999px; padding: 5px 9px; background: transparent; }
    #action-menu button:hover { background: #ece8df; }
    html[data-layout-mode="replay"] #action-menu { display: none !important; }
    html[data-layout-theme="dark"] { color-scheme: dark; }
    html[data-layout-theme="dark"] #action-menu:not([hidden]):not(:empty) { border-color: #59616b; background: rgba(31,35,41,.97); color: #e6e1d6; box-shadow: 0 8px 28px rgba(0,0,0,.42); }
    html[data-layout-theme="dark"] #action-menu button { color: #e6e1d6; }
    html[data-layout-theme="dark"] #action-menu button:hover { background: #343a43; }
    html[data-layout-theme="dark"] #companion-label { background: rgba(31,35,41,.9) !important; color: #e6e1d6 !important; }
    html[data-layout-theme="dark"] .vpa-spawn-column,
    html[data-layout-theme="dark"] .vpa-spawn-submenu,
    html[data-layout-theme="dark"] .vpa-spawn-row,
    html[data-layout-theme="dark"] .vpa-spawn-search,
    html[data-layout-theme="dark"] input[aria-label="Lambda term to spawn"] {
      border-color: #59616b !important; background: #1f2329 !important; color: #e6e1d6 !important;
    }
    html[data-layout-theme="dark"] .vpa-spawn-row:hover { background: #343a43 !important; }
    html[data-layout-aesthetic="carbon"] #action-menu,
    html[data-layout-aesthetic="carbon"] .vpa-spawn-column,
    html[data-layout-aesthetic="carbon"] .vpa-spawn-submenu { border-radius: 3px !important; font-family: "IBM Plex Sans", system-ui, sans-serif !important; }
    html[data-layout-aesthetic="basalt"] #action-menu,
    html[data-layout-aesthetic="basalt"] .vpa-spawn-column,
    html[data-layout-aesthetic="basalt"] .vpa-spawn-submenu,
    html[data-layout-aesthetic="basalt"] .vpa-spawn-search,
    html[data-layout-aesthetic="basalt"] .vpa-spawn-row { border-radius: 2px !important; font-family: "IBM Plex Mono", ui-monospace, monospace !important; }
    html[data-layout-aesthetic="porcelain"] #action-menu,
    html[data-layout-aesthetic="porcelain"] .vpa-spawn-column,
    html[data-layout-aesthetic="porcelain"] .vpa-spawn-submenu,
    html[data-layout-aesthetic="porcelain"] .vpa-spawn-search,
    html[data-layout-aesthetic="porcelain"] .vpa-spawn-row { border-radius: 8px !important; font-family: "IBM Plex Mono", ui-monospace, monospace !important; }
  `
  doc.head.append(appStyle)

  libraryBody.append(actualLibrary)
  const hideLibraryToggle = (): void => {
    const internalToggle = actualLibrary.querySelector(':scope > button')
    if (internalToggle !== null) internalToggle.setAttribute('hidden', '')
  }
  hideLibraryToggle()
  new MutationObserver(hideLibraryToggle).observe(actualLibrary, { childList: true })

  const clickActual = (label: string): void => {
    const actual = findButton(doc, label)
    if (actual === null) throw new Error(`the real shell no longer exposes '${label}'`)
    actual.click()
  }
  const dispatchAppKey = (key: string, init: KeyboardEventInit = {}): void => {
    const KeyboardEventCtor = (win as AppWindow & { KeyboardEvent: typeof KeyboardEvent }).KeyboardEvent
    win.dispatchEvent(new KeyboardEventCtor('keydown', { key, ...init }))
  }
  setLhs.addEventListener('click', () => clickActual('Set goal LHS'))
  setRhs.addEventListener('click', () => clickActual('Set goal RHS'))
  toggleMode.addEventListener('click', () => {
    const actual = findButton(doc, 'Switch to') ?? findButton(doc, 'Exit replay')
    if (actual === null) throw new Error('the real shell no longer exposes a mode transition')
    actual.click()
    setOpen('lifecycle', false)
  })
  theme.addEventListener('click', () => clickActual('Theme:'))
  companion.addEventListener('click', () => clickActual('Companion:'))
  undo.addEventListener('click', () => clickActual('Undo'))
  const replayRange = temporal.querySelector<HTMLInputElement>('.layout-time-range')
  const temporalBack = temporal.querySelector<HTMLButtonElement>('.layout-undo')
  const temporalForward = temporal.querySelector<HTMLButtonElement>('.layout-redo')
  if (replayRange === null || temporalBack === null || temporalForward === null) {
    throw new Error('the history surface is incomplete')
  }
  temporalBack.addEventListener('click', () => {
    if (win.__vpaDebug?.replay().mode === 'replay') dispatchAppKey('ArrowLeft')
    else clickActual('Undo')
  })
  temporalForward.addEventListener('click', () => {
    if (win.__vpaDebug?.replay().mode === 'replay') dispatchAppKey('ArrowRight')
    else dispatchAppKey('z', { ctrlKey: true, shiftKey: true })
  })
  replayRange.addEventListener('input', () => {
    const replayState = win.__vpaDebug?.replay()
    if (replayState?.mode !== 'replay') return
    const target = Number(replayRange.value)
    const delta = target - replayState.k
    const key = delta < 0 ? 'ArrowLeft' : 'ArrowRight'
    for (let step = 0; step < Math.abs(delta); step++) dispatchAppKey(key)
  })

  editStep.addEventListener('click', () => {
    const mode = win.__vpaDebug?.replay().mode
    if (mode !== 'edit') findButton(doc, mode === 'replay' ? 'Exit replay' : 'Switch to EDIT')?.click()
  })
  proveStep.addEventListener('click', () => {
    if (win.__vpaDebug?.replay().mode === 'edit') modeButton.click()
  })

  const synchronize = (): void => {
    const debug = win.__vpaDebug
    if (debug === undefined) return
    const replay = debug.replay()
    const mode = replay.mode.toUpperCase()
    const actualThemeLabel = findButton(doc, 'Theme:')?.textContent
    if (actualThemeLabel === undefined || actualThemeLabel === null) throw new Error('the real shell no longer exposes its theme state')
    const themeToken = actualThemeLabel.toLowerCase().includes('dark') ? 'dark' : 'light'
    host.dataset.theme = themeToken
    doc.documentElement.dataset.layoutTheme = themeToken
    doc.documentElement.dataset.layoutMode = replay.mode
    if (aesthetic !== undefined) doc.documentElement.dataset.layoutAesthetic = aesthetic
    modeButton.textContent = mode
    theme.textContent = actualThemeLabel
    companion.textContent = findButton(doc, 'Companion:')?.textContent ?? 'Companion view'
    toggleMode.textContent = replay.mode === 'edit' ? 'Enter proving' : replay.mode === 'prove' ? 'Return to editing' : 'Exit replay'
    temporal.hidden = replay.mode === 'edit'
    temporal.querySelector<HTMLElement>('.layout-time-label')!.textContent = replay.mode === 'replay'
      ? `${replay.k} / ${replay.n} · ${replay.label || 'start'}`
      : 'Proof history'
    replayRange.max = String(replay.n)
    replayRange.value = String(replay.k)
    replayRange.disabled = replay.mode !== 'replay' || replay.n === 0
    temporalBack.disabled = replay.mode === 'replay' && replay.k === 0
    temporalForward.disabled = replay.mode === 'replay' && replay.k === replay.n
    for (const step of [editStep, proveStep, replayStep]) step.classList.remove('is-current')
    ;(replay.mode === 'edit' ? editStep : replay.mode === 'prove' ? proveStep : replayStep).classList.add('is-current')
    replayStep.disabled = replay.mode !== 'replay'

    requestAnimationFrame(synchronize)
  }
  synchronize()
  host.dataset.ready = 'true'
}
