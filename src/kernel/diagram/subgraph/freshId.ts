/** Deterministic collision-dodging id: base, then base_0, base_1, … */
export function freshId(taken: ReadonlySet<string>, base: string): string {
  if (!taken.has(base)) return base
  for (let k = 0; ; k++) {
    const candidate = `${base}_${k}`
    if (!taken.has(candidate)) return candidate
  }
}
