import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'

const shellSource = readFileSync('src/app/shell.ts', 'utf8')
const viewportSource = readFileSync('src/interaction/controllers/viewport.ts', 'utf8')
const constructSource = readFileSync('src/interaction/construct.ts', 'utf8')
const spawnSource = readFileSync('src/interaction/spawn.ts', 'utf8')
const movesSource = readFileSync('src/app/interact/moves.ts', 'utf8')
const proofFrontSource = readFileSync('src/app/proof-front.ts', 'utf8')
const gameProofSurfaceSource = readFileSync('src/game/interface/proof-surface.ts', 'utf8')
const relationWorkspaceSource = readFileSync('src/interaction/relation-workspace.ts', 'utf8')

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
        `src/interaction/controllers/viewport.ts must install a ${event} listener`,
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

  it('makes both products consume the shared relation-workspace authority', () => {
    expect(proofFrontSource).toMatch(
      /from ['"]\.\.\/interaction\/relation-workspace['"]/,
    )
    expect(gameProofSurfaceSource).toMatch(
      /from ['"]\.\.\/\.\.\/interaction\/relation-workspace['"]/,
    )
    expect(gameProofSurfaceSource).toMatch(
      /from ['"]\.\.\/\.\.\/interaction\/relation-transactions['"]/,
    )
    expect(gameProofSurfaceSource).not.toMatch(/from ['"][^'"]*\/app(?:\/|['"])/)
  })

  it('leaves workspace keyboard and modifier arbitration with its own viewport', () => {
    expect(proofFrontSource).toContain('if (this.#relationWorkspace !== null) return false')
    expect(gameProofSurfaceSource).toContain('if (this.#abstraction !== null) return false')
    expect(relationWorkspaceSource).toContain(
      'modifiersChanged: (ctrlHeld) => this.modifiersChanged(ctrlHeld)',
    )
  })
})
