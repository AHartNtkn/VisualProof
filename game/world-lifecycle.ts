export async function commitWorldShutdown(
  shutdownBarrier: () => Promise<void>,
  invalidate: () => void,
): Promise<void> {
  await shutdownBarrier()
  invalidate()
}
