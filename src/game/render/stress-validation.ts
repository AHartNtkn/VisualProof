export type StressResidency = {
  readonly mode: 'game' | 'raw'
  readonly trees: number
  readonly visible: number
  readonly resident: number
  readonly full: number
  readonly representationErrors: number
  readonly representationError: string
}

export function assertStressResidency(row: StressResidency): void {
  if (row.representationErrors !== 0 || row.representationError.length !== 0) {
    throw new Error(
      `${row.mode} ${row.trees} representation failures (${row.representationErrors}): ${row.representationError}`,
    )
  }
  if (row.resident !== row.visible) {
    throw new Error(`${row.mode} ${row.trees} settled with ${row.resident} resident of ${row.visible} visible trees`)
  }
  if (row.mode === 'raw'
    && (row.visible !== row.trees || row.resident !== row.trees || row.full !== row.trees)) {
    throw new Error(
      `raw ${row.trees} settled with visible=${row.visible}, resident=${row.resident}, full=${row.full}`,
    )
  }
}
