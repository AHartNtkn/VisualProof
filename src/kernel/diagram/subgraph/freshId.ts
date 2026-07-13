export type IdReservation = {
  readonly regions: ReadonlySet<string>
  readonly nodes: ReadonlySet<string>
  readonly wires: ReadonlySet<string>
}

/** Deterministic collision-dodging id: base, then base_0, base_1, … */
export function freshId(
  taken: ReadonlySet<string>,
  base: string,
  reserved: ReadonlySet<string> = new Set(),
): string {
  if (!taken.has(base) && !reserved.has(base)) return base
  for (let k = 0; ; k++) {
    const candidate = `${base}_${k}`
    if (!taken.has(candidate) && !reserved.has(candidate)) return candidate
  }
}
