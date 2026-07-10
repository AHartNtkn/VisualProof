import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'

const shellSource = readFileSync('src/app/shell.ts', 'utf8')
const viewportSource = readFileSync('src/app/interact/viewport.ts', 'utf8')
const constructSource = readFileSync('src/app/interact/construct.ts', 'utf8')
const spawnSource = readFileSync('src/app/interact/spawn.ts', 'utf8')

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
})
