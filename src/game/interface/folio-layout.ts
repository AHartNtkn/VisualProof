import type { CultureId } from '../types'

export type ProductionInterfaceLayout = {
  readonly compact: boolean
  readonly folio: {
    readonly presentation: 'open' | 'drawer'
    readonly left: number
    readonly width: number
    readonly visibleHandle: number
  }
  readonly lens: {
    readonly left: number
    readonly top: number
    readonly size: number
  }
}

const SAFE_EDGE = 16
const COMPACT_BREAKPOINT = 980

export function clampSheetScroll(
  requested: number,
  sheetHeight: number,
  viewportHeight: number,
): number {
  const maximum = Math.max(0, sheetHeight - viewportHeight)
  return Math.min(maximum, Math.max(0, Number.isFinite(requested) ? requested : 0))
}

export function folioScrollForCulture(
  scrollByCulture: ReadonlyMap<CultureId, number>,
  culture: CultureId,
  sheetHeight: number,
  viewportHeight: number,
): number {
  return clampSheetScroll(scrollByCulture.get(culture) ?? 0, sheetHeight, viewportHeight)
}

export function interfaceLayout(width: number, height: number): ProductionInterfaceLayout {
  const safeWidth = Math.max(1, width)
  const safeHeight = Math.max(1, height)
  const compact = safeWidth < COMPACT_BREAKPOINT
  const visibleHandle = 52
  const folioWidth = compact
    ? Math.min(420, Math.max(visibleHandle, safeWidth - 48))
    : Math.min(420, Math.max(340, safeWidth * 0.28))
  const availableLeft = compact ? 0 : folioWidth
  const availableWidth = compact ? safeWidth : Math.max(1, safeWidth - folioWidth)
  const lensSize = Math.max(
    1,
    Math.min(safeHeight - SAFE_EDGE * 2, availableWidth - SAFE_EDGE * 2),
  )
  return {
    compact,
    folio: {
      presentation: compact ? 'drawer' : 'open',
      left: compact ? visibleHandle - folioWidth : 0,
      width: folioWidth,
      visibleHandle,
    },
    lens: {
      left: availableLeft + (availableWidth - lensSize) / 2,
      top: (safeHeight - lensSize) / 2,
      size: lensSize,
    },
  }
}
