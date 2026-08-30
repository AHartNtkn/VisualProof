import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import {
  LiveOrderCatalog,
  availableOrderIds,
  decodeOrderCatalog,
  openingOrderCatalog,
  type OrderCatalogRevision,
  validateOrderCatalog,
} from '../../../src/game/orders/catalog'
import { initialOrderProgress } from '../../../src/game/orders/session'

const openingOrderContent: unknown = JSON.parse(readFileSync(
  new URL('../../../game/content/orders.json', import.meta.url),
  'utf8',
))

function content(): Array<Record<string, unknown>> {
  return structuredClone(openingOrderContent) as Array<Record<string, unknown>>
}

describe('opening order catalog', () => {
  it('decodes the authored opening order sequence and dependencies', () => {
    // Catches a checked-in catalog that changes the opening progression or reward values.
    const revision = decodeOrderCatalog(openingOrderContent)

    expect(revision.definitions.map(({ id }) => id)).toEqual([
      'blank-sprout',
      'single-double-cut',
      'irregular-double-cut-a',
      'irregular-double-cut-b',
    ])
    expect(revision.definitions.map(({ reward }) => reward)).toEqual([1, 1, 1, 1])
    expect(revision.byId.get('blank-sprout')?.prerequisites).toEqual([])
    expect(revision.byId.get('single-double-cut')?.prerequisites).toEqual(['blank-sprout'])
    expect(revision.byId.get('irregular-double-cut-a')?.prerequisites).toEqual(['single-double-cut'])
    expect(revision.byId.get('irregular-double-cut-b')?.prerequisites).toEqual(['single-double-cut'])
  })

  it('rejects malformed catalog definitions before they become a revision', () => {
    // Catches malformed author content silently becoming an authoritative catalog.
    const cases: ReadonlyArray<{ readonly name: string; readonly value: unknown }> = [
      {
        name: 'duplicate ids',
        value: (() => {
          const value = content()
          value.push(structuredClone(value[0]!))
          return value
        })(),
      },
      {
        name: 'missing prerequisites',
        value: (() => {
          const value = content()
          value[0]!['prerequisites'] = ['missing']
          return value
        })(),
      },
      {
        name: 'self dependencies',
        value: (() => {
          const value = content()
          value[0]!['prerequisites'] = ['blank-sprout']
          return value
        })(),
      },
      {
        name: 'cycles',
        value: (() => {
          const value = content()
          value[0]!['prerequisites'] = ['single-double-cut']
          return value
        })(),
      },
      {
        name: 'negative rewards',
        value: (() => {
          const value = content()
          value[0]!['reward'] = -1
          return value
        })(),
      },
      {
        name: 'fractional rewards',
        value: (() => {
          const value = content()
          value[0]!['reward'] = 1.5
          return value
        })(),
      },
      {
        name: 'unknown fields',
        value: (() => {
          const value = content()
          value[0]!['extra'] = true
          return value
        })(),
      },
      {
        name: 'malformed diagrams',
        value: (() => {
          const value = content()
          value[0]!['goal'] = { regions: [] }
          return value
        })(),
      },
      {
        name: 'blank ids',
        value: (() => {
          const value = content()
          value[0]!['id'] = ''
          return value
        })(),
      },
    ]

    for (const { name, value } of cases) {
      expect(() => decodeOrderCatalog(value), name).toThrow()
    }
  })

  it('freezes valid definitions only after validating the complete dependency graph', () => {
    // Catches consumers being able to mutate a decoded definition after graph validation.
    const revision = decodeOrderCatalog(openingOrderContent)
    validateOrderCatalog(revision.definitions)

    expect(Object.isFrozen(revision.definitions[0]!)).toBe(true)
    expect(Object.isFrozen(revision.definitions[1]!.prerequisites)).toBe(true)
  })

  it('offers only allowed pending orders whose prerequisites are complete', () => {
    // Catches catalog availability exposing locked, accepted, or completed orders.
    const progress = initialOrderProgress(openingOrderCatalog.current.definitions)
    expect(availableOrderIds(progress, openingOrderCatalog.current, () => true)).toEqual(['blank-sprout'])
    expect(availableOrderIds(progress, openingOrderCatalog.current, (id) => id !== 'blank-sprout')).toEqual([])

    const accepted = {
      ...progress,
      orders: new Map(progress.orders).set('blank-sprout', {
        kind: 'accepted' as const,
        pot: { x: 0, z: 0, yaw: 0 },
      }),
    }
    expect(availableOrderIds(accepted, openingOrderCatalog.current, () => true)).toEqual([])

    const completed = {
      ...progress,
      orders: new Map(progress.orders).set('blank-sprout', { kind: 'completed' as const }),
    }
    expect(availableOrderIds(completed, openingOrderCatalog.current, () => true)).toEqual(['single-double-cut'])
  })

  it('does not expose a mutable map through a decoded revision', () => {
    // Catches a ReadonlyMap that is only compile-time readonly and can be mutated by a cast.
    const revision = decodeOrderCatalog(openingOrderContent)

    expect(() => (revision.byId as unknown as Map<string, unknown>).set('forged', {})).toThrow()
    expect(revision.byId.has('forged')).toBe(false)
  })

  it('notifies catalog subscribers only when a fully decoded revision is published', () => {
    // Catches malformed content notifying live consumers before a valid revision exists.
    const catalog = new LiveOrderCatalog(openingOrderCatalog.current)
    const observed: string[][] = []
    const dispose = catalog.subscribe((revision) => observed.push(revision.definitions.map(({ id }) => id)))
    const malformed = content()
    malformed[0]!['reward'] = -1
    const forged: OrderCatalogRevision = {
      definitions: openingOrderCatalog.current.definitions,
      byId: openingOrderCatalog.current.byId,
    }

    expect(() => decodeOrderCatalog(malformed)).toThrow()
    expect(() => catalog.publish(forged)).toThrow(/decoded/i)
    expect(observed).toEqual([])

    const revision = decodeOrderCatalog(openingOrderContent)
    catalog.publish(revision)
    expect(observed).toEqual([[
      'blank-sprout',
      'single-double-cut',
      'irregular-double-cut-a',
      'irregular-double-cut-b',
    ]])

    dispose()
    catalog.publish(revision)
    expect(observed).toHaveLength(1)
  })
})
