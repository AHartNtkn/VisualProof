import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { mkSelection } from '../../src/kernel/diagram/subgraph/selection'
import { applyConversion } from '../../src/kernel/rules/conversion'
import { parseTerm } from '../../src/kernel/term/parse'
import { weakHeadNormalize } from '../../src/kernel/term/hnf'
import { mkEngine } from '../../src/view/engine'
import { DARK } from '../../src/view/paint'
import {
  GameProofMotion,
  gameProofMotionPreferences,
} from '../../src/game/interface/proof-motion'

describe('game proof motion ownership', () => {
  it('delays animated conversion exactly once and commits non-conversion immediately', () => {
    const builder = new DiagramBuilder()
    const node = builder.termNode(builder.root, parseTerm('(\\x. x) y'))
    const diagram = builder.build()
    const engine = mkEngine(diagram, [])
    const target = weakHeadNormalize(diagram.nodes[node]!.kind === 'term' ? diagram.nodes[node]!.term : parseTerm('x'), 256).term
    const conversion = applyConversion(diagram, node, target, 256)
    const step = { rule: 'conversion' as const, node, term: target, certificate: conversion.certificate, attachments: {} }
    const motion = new GameProofMotion({
      preferences: () => gameProofMotionPreferences(false), diagram: () => diagram,
      engine: () => engine, theme: () => DARK,
    })
    let conversions = 0
    expect(motion.run(step, () => { conversions++ }, 0)).toBe(true)
    expect([motion.playing, conversions]).toEqual([true, 0])
    motion.frame(1_000_000)
    motion.frame(2_000_000)
    expect([motion.playing, conversions]).toEqual([false, 1])

    let immediate = 0
    const selection = mkSelection(diagram, { region: diagram.root, regions: [], nodes: [node], wires: [] })
    expect(motion.run({ rule: 'doubleCutIntro', sel: selection }, () => { immediate++ }, 0)).toBe(false)
    expect(immediate).toBe(1)
  })

  it('observes swaps and cancels an active delayed commit on disposal', () => {
    const builder = new DiagramBuilder()
    const node = builder.termNode(builder.root, parseTerm('(\\x. x) y'))
    const diagram = builder.build()
    const before = mkEngine(diagram, [])
    const emptyBuilder = new DiagramBuilder()
    const after = mkEngine(emptyBuilder.build(), [])
    const preferences = gameProofMotionPreferences(false)
    const motion = new GameProofMotion({ preferences: () => preferences, diagram: () => diagram, engine: () => before, theme: () => DARK })
    motion.observeSwap(before, after, 0)
    expect(motion.debug(1).ghosts).toBeGreaterThan(0)
    const target = weakHeadNormalize(diagram.nodes[node]!.kind === 'term' ? diagram.nodes[node]!.term : parseTerm('x'), 256).term
    const conversion = applyConversion(diagram, node, target, 256)
    let commits = 0
    motion.run({ rule: 'conversion', node, term: target, certificate: conversion.certificate, attachments: {} }, () => { commits++ }, 0)
    motion.dispose()
    motion.frame(1_000_000)
    expect([motion.playing, commits]).toEqual([false, 0])
  })
})
