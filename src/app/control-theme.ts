import type { ControlPalette, Theme } from '../view/paint'

export const CONTROL_THEME_PROPERTIES = [
  ['surface', '--vpa-control-surface'],
  ['foreground', '--vpa-control-foreground'],
  ['border', '--vpa-control-border'],
  ['hoverSurface', '--vpa-control-hover-surface'],
  ['activeSurface', '--vpa-control-active-surface'],
  ['primarySurface', '--vpa-control-primary-surface'],
  ['primaryForeground', '--vpa-control-primary-foreground'],
  ['primaryBorder', '--vpa-control-primary-border'],
  ['primaryHoverSurface', '--vpa-control-primary-hover-surface'],
  ['primaryActiveSurface', '--vpa-control-primary-active-surface'],
  ['disabledSurface', '--vpa-control-disabled-surface'],
  ['disabledForeground', '--vpa-control-disabled-foreground'],
  ['disabledBorder', '--vpa-control-disabled-border'],
  ['focusRing', '--vpa-control-focus-ring'],
  ['menuSurface', '--vpa-control-menu-surface'],
  ['menuHoverSurface', '--vpa-control-menu-hover-surface'],
  ['mutedForeground', '--vpa-control-muted-foreground'],
] as const satisfies readonly (readonly [keyof ControlPalette, `--vpa-${string}`])[]

export function applyControlTheme(document: Document, theme: Theme): void {
  const root = document.documentElement
  root.dataset.colorMode = theme.mode
  root.style.colorScheme = theme.mode
  for (const [key, property] of CONTROL_THEME_PROPERTIES) {
    root.style.setProperty(property, theme.controls[key])
  }
}
