import { readFileSync, readdirSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'

const shellSource = readFileSync('src/app/shell.ts', 'utf8')
const viewportSource = readFileSync('src/app/interact/viewport.ts', 'utf8')
const constructSource = readFileSync('src/app/interact/construct.ts', 'utf8')
const spawnSource = readFileSync('src/app/interact/spawn.ts', 'utf8')
const connectionSource = readFileSync('src/app/interact/connection.ts', 'utf8')
const movesSource = readFileSync('src/app/interact/moves.ts', 'utf8')
const appIndexSource = readFileSync('src/app/index.ts', 'utf8')

function productionTypeScriptFiles(directory: string): string[] {
  return readdirSync(directory, { withFileTypes: true })
    .flatMap((entry) => {
      const path = join(directory, entry.name)
      return entry.isDirectory()
        ? productionTypeScriptFiles(path)
        : entry.isFile() && entry.name.endsWith('.ts') ? [path] : []
    })
    .sort()
}

type ProductionSource = {
  readonly path: string
  readonly source: string
}

const productionAppSources: readonly ProductionSource[] =
  productionTypeScriptFiles('src/app').map((path) => ({
    path,
    source: readFileSync(path, 'utf8'),
  }))

function displacedRelationInputViolations(
  sources: readonly ProductionSource[],
): string[] {
  const violations: string[] = []
  const globallyDisplaced = [
    /relationJoinStep/,
    /relationSeverStep/,
    /wire-content-and-parameters/,
    /scope-and-occurrences/,
    /Join relation content/,
    /Sever relation/,
    /relationOccurrencePicker/,
    /relationOccurrenceCandidates/,
    /discoverRelationOccurrences/,
    /findRelationOccurrences/,
    /inferRelationOccurrences/,
    /PreparedMembrane/,
    /prepareMembraneContent/,
    /membraneCrossing/,
    /PendingMembrane/,
    /crossing tap/i,
  ] as const
  for (const { path, source } of sources) {
    for (const pattern of globallyDisplaced) {
      if (pattern.test(source)) violations.push(`${path}: ${pattern.source}`)
    }
    if (path !== 'src/app/interact/connection.ts') {
      for (const kind of ['relationJoin', 'relationSever']) {
        if (new RegExp(`kind:\\s*['"]${kind}['"]`).test(source)) {
          violations.push(`${path}: ${kind} gesture discriminator`)
        }
      }
      if (/kind:\s*['"]relation['"]/.test(source)) {
        violations.push(`${path}: relation durable-input discriminator`)
      }
    }
  }
  return violations
}

const canvasInteractionEvents = [
  'pointerdown', 'pointermove', 'pointerup', 'pointercancel',
  'lostpointercapture', 'pointerleave', 'contextmenu', 'dblclick', 'wheel',
] as const

function listenerPattern(event: string): RegExp {
  return new RegExp(`\\.addEventListener\\(\\s*['\"]${event}['\"]`)
}

describe('production interaction ownership', () => {
  it('keeps the shell free of the retired interaction controller', () => {
    for (const retiredName of [
      'interactionPrototype',
      'projectDragToSemanticFrontier',
      'commitBodyPositions',
    ]) {
      expect(shellSource, `src/app/shell.ts still contains ${retiredName}`).not.toContain(retiredName)
    }

    for (const event of canvasInteractionEvents) {
      expect(
        listenerPattern(event).test(shellSource),
        `src/app/shell.ts still installs a ${event} listener`,
      ).toBe(false)
    }
  })

  it('assigns production canvas interaction listeners to the viewport controller', () => {
    for (const event of canvasInteractionEvents) {
      expect(
        listenerPattern(event).test(viewportSource),
        `src/app/interact/viewport.ts must install a ${event} listener`,
      ).toBe(true)
    }
    for (const event of ['keydown', 'keyup']) {
      expect(listenerPattern(event).test(viewportSource), `viewport must own ${event}`).toBe(true)
    }
  })

  it('keeps construction policy and the spawn cascade free of global interaction lifecycles', () => {
    for (const [name, source] of [['construct', constructSource], ['spawn', spawnSource]] as const) {
      expect(source, `${name} must not listen on window`).not.toMatch(/window\.addEventListener/)
      expect(source, `${name} must not listen on document`).not.toMatch(/document\.addEventListener/)
      expect(source, `${name} must not listen on canvas`).not.toMatch(/canvas\.addEventListener/)
    }
  })

  it('does not retain the retired edit construction buttons', () => {
    for (const label of [
      'Add term', 'Add relation', 'Wrap in cut', 'Wrap in bubble',
      'Delete selection', 'Join two wires',
    ]) expect(shellSource).not.toContain(`button('${label}'`)
  })

  it('keeps severing on the slash gesture with no double-click mode', () => {
    for (const displaced of ['severMode', 'double-click strand', 'vpa-sever-option']) {
      expect(constructSource, `construction retains ${displaced}`).not.toContain(displaced)
      expect(shellSource, `shell retains ${displaced}`).not.toContain(displaced)
    }
  })

  it('has one shared proof controller and no backward/manual-picker interaction authority', () => {
    expect(shellSource.match(/new ProofMoveController/g)).toHaveLength(1)
    for (const displaced of [
      'type BackwardEntry',
      'backwardEntries',
      'commitBackward',
      "kind: 'unCite'",
      "kind: 'cite'",
      "kind: 'iterate'; readonly sel",
    ]) expect(shellSource, `shell retains displaced proof path ${displaced}`).not.toContain(displaced)
    expect(movesSource).not.toMatch(/window\.addEventListener|document\.addEventListener|canvas\.addEventListener/)
  })

  it('keeps relation quantifiers out of action menus and standalone constructors', () => {
    const actionsSource = readFileSync('src/app/actions.ts', 'utf8')
    for (const displaced of [
      "kind: 'relationJoin'",
      "kind: 'relationSever'",
      'wire-content-and-parameters',
      'scope-and-occurrences',
      'Join relation content',
      'Sever relation',
      'relationJoinStep',
      'relationSeverStep',
    ]) {
      expect(actionsSource + movesSource, `retains displaced relation input path ${displaced}`)
        .not.toContain(displaced)
    }
    expect(displacedRelationInputViolations(productionAppSources)).toEqual([])
    for (const kind of ['relationJoin', 'relationSever']) {
      expect(
        connectionSource.match(new RegExp(`kind:\\s*['"]${kind}['"]`, 'g')),
        `connection must contain only its ${kind} union variant and emission`,
      ).toHaveLength(2)
      expect(
        movesSource.match(new RegExp(`case\\s+['"]${kind}['"]`, 'g')),
        `moves must contain exactly one ${kind} durable-step branch`,
      ).toHaveLength(1)
    }
    expect(
      connectionSource.match(/kind:\s*['"]relation['"]/g),
      'connection must exclusively own two relation input types and two emissions',
    ).toHaveLength(4)
    expect(appIndexSource).not.toMatch(
      /ConnectionDragController|ProofMoveController|relationJoin|relationSever/,
    )
  })

  it('keeps structural occurrence designation in the one ordered selection ledger', () => {
    const brushSource = readFileSync('src/app/interact/brush.ts', 'utf8')
    expect(connectionSource).toContain('prepareSelectedOccurrences')
    expect(connectionSource).not.toMatch(
      /export function prepareSelectedOccurrence\s*\(/,
    )
    expect(connectionSource).not.toContain('setSelection([])')
    expect(connectionSource).toContain('relationSelection')
    expect(movesSource).toContain('selection: options.selection')
    expect(movesSource).toContain('setSelection: options.setSelection')
    expect(brushSource).toContain('[...selected, hit]')
    expect(displacedRelationInputViolations(productionAppSources)).toEqual([])
  })

  it('detects a competing relation input path anywhere in the production app surface', () => {
    expect(displacedRelationInputViolations([{
      path: 'src/app/interact/competing.ts',
      source: `
        export type Competing = { kind: 'relationJoin' }
        export function relationSeverStep() {
          return { rule: 'wireSever', input: { kind: 'relation' } }
        }
      `,
    }])).toEqual([
      'src/app/interact/competing.ts: relationSeverStep',
      'src/app/interact/competing.ts: relationJoin gesture discriminator',
      'src/app/interact/competing.ts: relation durable-input discriminator',
    ])
  })
})
