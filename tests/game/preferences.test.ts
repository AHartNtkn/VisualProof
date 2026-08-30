import { describe, expect, it } from 'vitest'
import { DeveloperPreferences } from '../../game/preferences'

class TestStorage {
  readonly #values: Map<string, string>
  readonly setCalls: Array<readonly [string, string]> = []

  constructor(entries: readonly (readonly [string, string])[] = []) {
    this.#values = new Map(entries)
  }

  getItem(key: string): string | null {
    return this.#values.get(key) ?? null
  }

  setItem(key: string, value: string): void {
    this.setCalls.push([key, value])
    this.#values.set(key, value)
  }
}

describe('developer preferences', () => {
  it.each([null, '', 'TRUE', '1', '{"enabled":true}'])(
    'defaults a missing or invalid stored value %j to disabled',
    (stored) => {
      // Catches malformed application state granting developer access.
      const storage = new TestStorage()
      if (stored !== null) storage.setItem('orchard.developerTools', stored)

      expect(new DeveloperPreferences(storage).developerToolsEnabled).toBe(false)
    },
  )

  it('persists Developer Tools for a new preference instance', () => {
    // Catches the setting being held only in one controller session.
    const storage = new TestStorage()
    new DeveloperPreferences(storage).setDeveloperToolsEnabled(true)

    expect(new DeveloperPreferences(storage).developerToolsEnabled).toBe(true)
    expect(storage.setCalls).toEqual([['orchard.developerTools', 'true']])
  })

  it('reads an exact true value from the application preference key', () => {
    // Catches reads consulting another key or treating the persisted true value as malformed.
    const storage = new TestStorage([['orchard.developerTools', 'true']])

    expect(new DeveloperPreferences(storage).developerToolsEnabled).toBe(true)
  })
})
