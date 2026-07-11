import { describe, expect, it } from 'vitest'
import { readFileSync } from 'node:fs'
import { gameBoundaryOffenders, tsFilesUnder } from './game-boundary-helpers'

describe('game package boundary analyzer', () => {
  const nestedFile = 'src/game/deep/nested/example.ts'

  it.each([
    ['static imports at arbitrary depth', "import product from '../../../app/product'", '../../../app/product'],
    ['side-effect directory-root imports', "import '../../../theories'", '../../../theories'],
    ['directory-root re-exports', "export * from '../../../app'", '../../../app'],
    ['dynamic imports', "const catalog = import('../../../theories/catalog')", '../../../theories/catalog'],
    ['Node filesystem imports', "import { readFileSync } from 'node:fs'", 'node:fs'],
    ['unprefixed filesystem imports', "const fs = import('fs')", 'fs'],
    ['project filesystem authority', "export { open } from '../../../fsaccess'", '../../../fsaccess'],
  ])('detects %s', (_label, source, specifier) => {
    expect(gameBoundaryOffenders(nestedFile, source)).toEqual([
      `${nestedFile} imports '${specifier}'`,
    ])
  })

  it('ignores allowed imports and import-shaped comments or strings', () => {
    const source = `
      import type { Diagram } from '../../../kernel/diagram/diagram'
      // import forbidden from '../../../app/product'
      const example = "import('../../../theories')"
    `
    expect(gameBoundaryOffenders(nestedFile, source)).toEqual([])
  })

  it.each([
    ['an identifier', "const target = '../../../app/product'; import(target)"],
    ['an interpolated template', "const area = 'app'; import(`../../../${area}/product`)"],
    ['a static template', 'import(`../../../app/product`)'],
  ])('rejects dynamic import from %s', (_label, source) => {
    expect(gameBoundaryOffenders(nestedFile, source)).toEqual([
      `${nestedFile} has a non-literal dynamic import`,
    ])
  })
})

describe('game package boundary', () => {
  it('never imports product, prototype-theory, or filesystem authority', () => {
    const offenders = tsFilesUnder('src/game').flatMap((file) => (
      gameBoundaryOffenders(file, readFileSync(file, 'utf8'))
    ))
    expect(offenders, offenders.join('\n')).toEqual([])
  })
})
