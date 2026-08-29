const SLOT_ID = /^[A-Za-z0-9_-]{1,64}$/

export function validateNativeSlotId(slotId: string): string {
  if (!SLOT_ID.test(slotId)) throw new Error(`invalid slot id '${slotId}'`)
  return slotId
}
