import type { Theme } from '../src/view/paint'

export type AestheticId = 'carbon' | 'basalt' | 'porcelain'

export const AESTHETIC_THEMES: Readonly<Record<AestheticId, readonly [Theme, Theme]>> = {
  carbon: [
    {
      name: 'Carbon Light', canvas: '#f3f0e8', paper: '#faf8f1', ink: '#181b1c', frame: '#746c5f',
      wire: '#263034', wireW: 2.05, negFill: 'rgba(77, 67, 49, .10)', rimW: 1.35,
      discFill: '#fdfaf2', discText: '#181b1c', font: 'Charter, Georgia, serif',
      insetColor: 'rgba(55, 45, 29, .13)', wireGlow: false, bubbleLightness: 44,
      interaction: {
        selection: '#1a5fff', hover: '#5281e8', selectedHover: '#123f9c', pin: '#986400',
        valid: '#087f5b', validWash: '#087f5b14', refusal: '#c53632',
      },
    },
    {
      name: 'Carbon Dark', canvas: '#15191a', paper: '#202526', ink: '#f0ede4', frame: '#596161',
      wire: '#ece7dd', wireW: 1.95, negFill: 'rgba(255, 255, 255, .055)', rimW: 1.25,
      discFill: '#272c2d', discText: '#f0ede4', font: 'Charter, Georgia, serif',
      insetColor: 'rgba(0, 0, 0, .34)', wireGlow: false, bubbleLightness: 65,
      interaction: {
        selection: '#78a5ff', hover: '#a4bfff', selectedHover: '#d1dcff', pin: '#e7b55a',
        valid: '#59d5a5', validWash: '#59d5a518', refusal: '#ff7b73',
      },
    },
  ],
  basalt: [
    {
      name: 'Basalt Light', canvas: '#eef0ec', paper: '#f8f9f6', ink: '#202629', frame: '#667174',
      wire: '#283033', wireW: 1.8, negFill: 'rgba(42, 58, 59, .08)', rimW: 1.15,
      discFill: '#fbfcf9', discText: '#202629', font: 'IBM Plex Mono, ui-monospace, monospace',
      insetColor: 'rgba(28, 42, 43, .12)', wireGlow: false, bubbleLightness: 42,
      interaction: {
        selection: '#00776b', hover: '#28998b', selectedHover: '#005b53', pin: '#855700',
        valid: '#176f4b', validWash: '#176f4b14', refusal: '#ad352f',
      },
    },
    {
      name: 'Basalt Dark', canvas: '#111518', paper: '#191e21', ink: '#edf1ef', frame: '#465154',
      wire: '#76d8dc', wireW: 1.75, negFill: 'rgba(255, 255, 255, .045)', rimW: 1.1,
      discFill: '#20272a', discText: '#edf1ef', font: 'IBM Plex Mono, ui-monospace, monospace',
      insetColor: 'rgba(0, 0, 0, .38)', wireGlow: true, bubbleLightness: 62,
      interaction: {
        selection: '#62e2c1', hover: '#8cf1d8', selectedHover: '#c5ffed', pin: '#ffc264',
        valid: '#67dda5', validWash: '#67dda518', refusal: '#ff756f',
      },
    },
  ],
  porcelain: [
    {
      name: 'Porcelain Light', canvas: '#f4f2ec', paper: '#fbfaf6', ink: '#20262b', frame: '#72797b',
      wire: '#26343a', wireW: 1.55, negFill: 'rgba(48, 64, 70, .075)', rimW: 1.15,
      discFill: '#fffefa', discText: '#20262b', font: 'IBM Plex Mono, ui-monospace, monospace',
      insetColor: 'rgba(38, 51, 57, .11)', wireGlow: false, bubbleLightness: 47,
      interaction: {
        selection: '#d97706', hover: '#5a7fbd', selectedHover: '#92400e', pin: '#7a5600',
        valid: '#08796b', validWash: '#08796b12', refusal: '#ac3038',
      },
    },
    {
      name: 'Porcelain Dark', canvas: '#121719', paper: '#1a2023', ink: '#edf0ea', frame: '#4b5559',
      wire: '#dce3e0', wireW: 1.5, negFill: 'rgba(255, 255, 255, .04)', rimW: 1.05,
      discFill: '#22292d', discText: '#edf0ea', font: 'IBM Plex Mono, ui-monospace, monospace',
      insetColor: 'rgba(0, 0, 0, .32)', wireGlow: false, bubbleLightness: 67,
      interaction: {
        selection: '#f59e0b', hover: '#adc2ff', selectedHover: '#fbbf24', pin: '#e4bb63',
        valid: '#51cebb', validWash: '#51cebb16', refusal: '#ff8b86',
      },
    },
  ],
}

export function aestheticId(value: string | null): AestheticId {
  if (value === 'carbon' || value === 'basalt' || value === 'porcelain') return value
  throw new Error(`unknown aesthetic '${value ?? ''}'`)
}
