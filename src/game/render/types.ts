import type { WireId } from '../../kernel/diagram/diagram'
import type { Scene3 } from '../../view3d/scene'
import type { Vec3 } from '../../view3d/vec3'

export type DisplayCameraPose = {
  readonly eye: Vec3
  readonly forward: Vec3
}

export type TreeLodAssets = {
  readonly full: Scene3
  readonly reduced: Scene3
  readonly marker: { readonly color: string; readonly size: number }
}

export type TreeRenderPalette = {
  readonly branch: string
  readonly cutBranch: string
  readonly baseWire: string
}

export type TreeRenderAsset = {
  readonly bounds: { readonly center: Vec3; readonly radius: number }
  readonly lods: TreeLodAssets
  readonly hues: readonly (readonly [WireId, string])[]
  readonly palette: TreeRenderPalette
  readonly widths: { readonly branch: 0.10; readonly curve: 0.05 }
  readonly glow: {
    readonly color: '#ffffff'
    readonly radius: 32
    readonly opacity: 0.65
    readonly bloom: 0.8
  }
}
