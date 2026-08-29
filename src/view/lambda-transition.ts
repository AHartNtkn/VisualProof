import type { Diagram, NodeId } from '../kernel/diagram/diagram'
import type { ProofAction } from '../kernel/proof/action'
import { termEq } from '../kernel/term/term'
import { planBetaMotion, type LambdaMotionPlan } from './lambda-motion'

export type LambdaMotionTransition = {
  readonly node: NodeId
  readonly plan: LambdaMotionPlan
  readonly direction: 'forward' | 'reverse'
}

/** Derive structural Lambda motion from the exact committed proof action. */
export function lambdaMotionFromAction(
  before: Diagram,
  after: Diagram,
  action: ProofAction,
  direction: 'forward' | 'reverse' = 'forward',
): LambdaMotionTransition | null {
  if (action.steps.length !== 1) return null
  const conversion = action.steps[0]
  if (
    conversion?.rule !== 'lambdaConversion'
    || conversion.certificate.leftSteps.length !== 1
    || conversion.certificate.rightSteps.length !== 0
  ) return null
  const reduction = conversion.certificate.leftSteps[0]!
  if (reduction.kind !== 'beta') return null

  const sourceDiagram = direction === 'forward' ? before : after
  const targetDiagram = direction === 'forward' ? after : before
  const source = sourceDiagram.nodes[conversion.node]
  const target = targetDiagram.nodes[conversion.node]
  if (source?.kind !== 'term' || target?.kind !== 'term') return null

  const sourceToTarget = conversion.correspondence.left.map((column) =>
    conversion.correspondence.right.indexOf(column))
  const plan = planBetaMotion(
    source.term,
    reduction,
    source.freeArity,
    target.freeArity,
    sourceToTarget,
  )
  if (!termEq(plan.target, conversion.term) || !termEq(plan.target, target.term)) {
    throw new Error('Lambda motion target does not match the committed beta conversion')
  }
  return { node: conversion.node, plan, direction }
}
