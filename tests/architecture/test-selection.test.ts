import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import defaultConfig from '../../vitest.config'
import physicsConfig from '../../vitest.physics.config'

const physicsBattery = [
  'tests/view/constraints.test.ts',
  'tests/view/drag-clamp.test.ts',
  'tests/view/elastica.test.ts',
  'tests/view/mec.test.ts',
  'tests/view/physics-drag.test.ts',
  'tests/view/relax.test.ts',
  'tests/view/wirephys.test.ts',
  'tests/view/wires.test.ts',
]

type TestConfig = {
  test?: {
    include?: string[]
    exclude?: string[]
  }
}

describe('test-suite selection policy', () => {
  it('keeps the dedicated physics batteries out of the default suite', () => {
    const exclude = (defaultConfig as TestConfig).test?.exclude ?? []
    expect(exclude.filter((file) => file.startsWith('tests/view/'))).toEqual(physicsBattery)
  })

  it('provides an explicit command containing exactly the physics batteries', () => {
    const include = (physicsConfig as TestConfig).test?.include ?? []
    expect(include).toEqual(physicsBattery)

    const pkg = JSON.parse(readFileSync('package.json', 'utf8')) as {
      scripts?: Record<string, string>
    }
    expect(pkg.scripts?.['test:physics']).toBe('vitest run --config vitest.physics.config.ts')
  })
})
