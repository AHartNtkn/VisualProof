export type CompassSurface = 'lifecycle' | 'library' | 'utilities'

export type CompassAperture = {
  readonly root: HTMLElement
  readonly status: HTMLElement
  readonly lifecycle: HTMLElement
  readonly libraryBody: HTMLElement
  readonly utilities: HTMLElement
  readonly temporalHost: HTMLElement
  setMode(label: string): void
  setOpen(surface: CompassSurface, open: boolean): void
  dispose(): void
}

const makeButton = (label: string, className: string): HTMLButtonElement => {
  const button = document.createElement('button')
  button.type = 'button'
  button.className = className
  button.textContent = label
  return button
}

export function mountCompass(host: HTMLElement): CompassAperture {
  host.replaceChildren()
  host.className = 'vpa-compass'

  const north = document.createElement('nav')
  north.className = 'vpa-compass-north'
  north.setAttribute('aria-label', 'Application controls')
  const modeButton = makeButton('Mode: Edit', 'vpa-compass-mode')
  modeButton.setAttribute('aria-expanded', 'false')
  const libraryButton = makeButton('Library', 'vpa-compass-library')
  libraryButton.setAttribute('aria-expanded', 'true')
  const utilitiesButton = makeButton('Utilities', 'vpa-compass-utilities')
  utilitiesButton.setAttribute('aria-expanded', 'false')
  const status = document.createElement('output')
  status.id = 'status'
  status.className = 'vpa-status'
  north.append(modeButton, status, libraryButton, utilitiesButton)

  const lifecycle = document.createElement('section')
  lifecycle.className = 'vpa-compass-surface vpa-lifecycle'
  lifecycle.setAttribute('aria-label', 'Proof lifecycle')
  lifecycle.hidden = true

  const library = document.createElement('aside')
  library.className = 'vpa-compass-surface vpa-ledger'
  library.setAttribute('role', 'complementary')
  library.setAttribute('aria-label', 'Library')
  const libraryHead = document.createElement('header')
  const libraryTitle = document.createElement('span')
  libraryTitle.innerHTML = '<b>Library</b><small>Verified knowledge and sources</small>'
  const closeLibrary = makeButton('×', 'vpa-surface-close')
  closeLibrary.setAttribute('aria-label', 'Close library')
  libraryHead.append(libraryTitle, closeLibrary)
  const libraryBody = document.createElement('div')
  libraryBody.className = 'vpa-ledger-body'
  library.append(libraryHead, libraryBody)

  const utilities = document.createElement('section')
  utilities.className = 'vpa-compass-surface vpa-utility-surface'
  utilities.setAttribute('aria-label', 'Utilities')
  utilities.hidden = true

  const temporalHost = document.createElement('div')
  temporalHost.className = 'vpa-compass-south'
  host.append(north, lifecycle, library, utilities, temporalHost)

  const triggers: Record<CompassSurface, HTMLButtonElement> = {
    lifecycle: modeButton,
    library: libraryButton,
    utilities: utilitiesButton,
  }
  const surfaces: Record<CompassSurface, HTMLElement> = { lifecycle, library, utilities }
  const listeners: Array<() => void> = []
  const listen = (target: EventTarget, type: string, listener: EventListener): void => {
    target.addEventListener(type, listener)
    listeners.push(() => target.removeEventListener(type, listener))
  }
  const setOpen = (surface: CompassSurface, open: boolean): void => {
    for (const name of Object.keys(surfaces) as CompassSurface[]) {
      const show = name === surface && open
      surfaces[name].hidden = !show
      triggers[name].setAttribute('aria-expanded', String(show))
    }
  }
  for (const name of Object.keys(triggers) as CompassSurface[]) {
    listen(triggers[name], 'click', () => setOpen(name, surfaces[name].hidden))
  }
  listen(closeLibrary, 'click', () => setOpen('library', false))

  return {
    root: host,
    status,
    lifecycle,
    libraryBody,
    utilities,
    temporalHost,
    setMode: (label) => { modeButton.textContent = `Mode: ${label}` },
    setOpen,
    dispose: () => {
      for (const dispose of listeners.splice(0)) dispose()
      host.replaceChildren()
      host.className = ''
    },
  }
}
