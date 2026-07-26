export function theoremActionCountLabel(count: number): string {
  return `${count} action${count === 1 ? '' : 's'}`
}
