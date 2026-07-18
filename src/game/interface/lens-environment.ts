import { interfaceLayout } from './folio-layout'
import { substratePresentation } from './substrate-presentation'
import './lens-environment.css'

export type LensEnvironmentOptions = {
  readonly host: HTMLElement
  readonly substrateSeed: string
  readonly width: number
  readonly height: number
}

export type MountedLensEnvironment = {
  readonly element: HTMLElement
  readonly proofCanvasSlot: HTMLElement
  readonly timelineHandleSlot: HTMLElement
  readonly folioHost: HTMLElement
  setLayout(width: number, height: number): void
  setSubstrateSeed(seed: string): void
  dispose(): void
}

const deskAsset = new URL('../../../assets/interface/generated/desk/natural-indigo-hardwood.png', import.meta.url)
const gasketAsset = new URL('../../../assets/interface/generated/central-lens/gasket-frame.png', import.meta.url)
const timelineHousingAsset = new URL('../../../assets/interface/generated/central-lens/timeline-housing.png', import.meta.url)
const timelineHandleAsset = new URL('../../../assets/interface/generated/central-lens/timeline-handle.png', import.meta.url)
const substrateAsset = new URL('../../../assets/interface/generated/substrates/static-review-substrate.png', import.meta.url)

const element = <K extends keyof HTMLElementTagNameMap>(
  document: Document,
  tag: K,
  className: string,
): HTMLElementTagNameMap[K] => {
  const created = document.createElement(tag)
  created.className = className
  return created
}

const decoration = (document: Document, className: string, asset: URL): HTMLImageElement => {
  const image = element(document, 'img', `${className} curse-decoration`)
  image.src = asset.href
  image.alt = ''
  image.setAttribute('aria-hidden', 'true')
  return image
}

export function mountLensEnvironment(options: LensEnvironmentOptions): MountedLensEnvironment {
  const document = options.host.ownerDocument
  const root = element(document, 'section', 'curse-production-environment')
  const desk = element(document, 'div', 'curse-production-desk')
  desk.setAttribute('aria-hidden', 'true')
  desk.style.setProperty('--curse-desk-image', `url("${deskAsset.href}")`)

  const stage = element(document, 'section', 'curse-production-lens')
  stage.setAttribute('aria-label', 'Seal examination lens')
  const substrate = decoration(document, 'curse-production-substrate', substrateAsset)
  const proofCanvasSlot = element(document, 'div', 'curse-production-proof-slot')
  const gasket = decoration(document, 'curse-production-gasket', gasketAsset)
  const timeline = element(document, 'div', 'curse-production-timeline')
  const timelineHousing = decoration(
    document,
    'curse-production-timeline-housing',
    timelineHousingAsset,
  )
  const timelineHandleSlot = element(document, 'div', 'curse-production-timeline-handle-slot')
  const timelineHandle = decoration(
    document,
    'curse-production-timeline-handle',
    timelineHandleAsset,
  )
  timelineHandleSlot.append(timelineHandle)
  timeline.append(timelineHousing, timelineHandleSlot)
  stage.append(substrate, proofCanvasSlot, gasket, timeline)

  const folioHost = element(document, 'aside', 'curse-production-folio-host')
  folioHost.setAttribute('aria-label', 'Excavation archive')
  root.append(desk, stage, folioHost)
  options.host.append(root)

  const setLayout = (width: number, height: number): void => {
    const layout = interfaceLayout(width, height)
    root.dataset.layout = layout.compact ? 'compact' : 'desktop'
    root.dataset.folioPresentation = layout.folio.presentation
    stage.style.setProperty('--curse-lens-left', `${layout.lens.left}px`)
    stage.style.setProperty('--curse-lens-top', `${layout.lens.top}px`)
    stage.style.setProperty('--curse-lens-size', `${layout.lens.size}px`)
    folioHost.style.setProperty('--curse-folio-left', `${layout.folio.left}px`)
    folioHost.style.setProperty('--curse-folio-width', `${layout.folio.width}px`)
    folioHost.style.setProperty('--curse-folio-handle', `${layout.folio.visibleHandle}px`)
  }
  const setSubstrateSeed = (seed: string): void => {
    const presentation = substratePresentation(seed)
    substrate.style.setProperty('--curse-substrate-x', `${presentation.positionX}%`)
    substrate.style.setProperty('--curse-substrate-y', `${presentation.positionY}%`)
    substrate.style.setProperty('--curse-substrate-rotation', `${presentation.rotationDegrees}deg`)
    substrate.style.setProperty('--curse-substrate-hue', `${presentation.hueDegrees}deg`)
    substrate.style.setProperty('--curse-substrate-saturation', `${presentation.saturation}`)
    substrate.style.setProperty('--curse-substrate-brightness', `${presentation.brightness}`)
    substrate.style.setProperty('--curse-substrate-scale', `${presentation.scale}`)
  }
  setLayout(options.width, options.height)
  setSubstrateSeed(options.substrateSeed)

  let disposed = false
  return {
    element: root,
    proofCanvasSlot,
    timelineHandleSlot,
    folioHost,
    setLayout,
    setSubstrateSeed,
    dispose() {
      if (disposed) return
      disposed = true
      root.remove()
    },
  }
}
