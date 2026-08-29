import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import { IOTA } from '../kernel/diagram/sig'
import {
  atom,
  biconditional,
  disjunction,
  emptyGraph,
  finishDiagram,
  identity,
  implication,
  negation,
  quantifierScope,
  type GraphConstruction,
} from '../theories/graph'
import { parseFormula } from './parse'
import type { Formula, FormulaOperand } from './syntax'

type TranslationState = {
  readonly graph: GraphConstruction
  readonly bindings: ReadonlyMap<string, WireId>
}

function boundWire(bindings: ReadonlyMap<string, WireId>, name: string): WireId {
  const wire = bindings.get(name)
  if (wire === undefined) throw new Error(`formula translation: unbound name '${name}'`)
  return wire
}

function operandWire(
  operand: FormulaOperand,
  state: TranslationState,
  region: RegionId,
): { readonly state: TranslationState; readonly wire: WireId } {
  if (operand.kind === 'reference') {
    return { state, wire: boundWire(state.bindings, operand.name) }
  }

  const graph = state.graph
  const node = `n${graph.nextNode}`
  const output = `w${graph.nextWire}`
  const nodes = {
    ...graph.nodes,
    [node]: {
      kind: 'term' as const,
      region,
      term: operand.parsed.term,
      freeArity: operand.parsed.freeIdentifiers.length,
    },
  }
  const wires = {
    ...graph.wires,
    [output]: {
      sig: IOTA,
      endpoints: Object.freeze([{ node, port: { kind: 'output' as const } }]),
    },
  }
  operand.parsed.freeIdentifiers.forEach((identifier, index) => {
    const wire = boundWire(state.bindings, identifier)
    const existing = wires[wire]
    if (existing === undefined) throw new Error(`formula translation: missing wire '${wire}'`)
    wires[wire] = {
      sig: existing.sig,
      endpoints: Object.freeze([
        ...existing.endpoints,
        { node, port: { kind: 'free' as const, index } },
      ]),
    }
  })
  const nextGraph: GraphConstruction = Object.freeze({
    ...graph,
    nodes: Object.freeze(nodes),
    wires: Object.freeze(wires),
    scopes: Object.freeze({ ...graph.scopes, [output]: region }),
    nextNode: graph.nextNode + 1,
    nextWire: graph.nextWire + 1,
  })
  return { state: { ...state, graph: nextGraph }, wire: output }
}

function drawFormula(
  formula: Formula,
  state: TranslationState,
  region: RegionId,
): TranslationState {
  switch (formula.kind) {
    case 'atom': {
      const relation = boundWire(state.bindings, formula.name)
      let operandState = state
      const args: WireId[] = []
      for (const operand of formula.args) {
        const translated = operandWire(operand, operandState, region)
        operandState = translated.state
        args.push(translated.wire)
      }
      return { ...operandState, graph: atom(operandState.graph, region, relation, args).graph }
    }
    case 'equality': {
      let operandState = state
      const wires: WireId[] = []
      for (const operand of formula.operands) {
        const translated = operandWire(operand, operandState, region)
        operandState = translated.state
        wires.push(translated.wire)
      }
      return { ...operandState, graph: identity(operandState.graph, region, wires).graph }
    }
    case 'and':
      return drawFormula(formula.right, drawFormula(formula.left, state, region), region)
    case 'not': {
      const scope = negation(state.graph, region)
      return drawFormula(formula.body, { ...state, graph: scope.graph }, scope.value)
    }
    case 'or': {
      const scope = disjunction(state.graph, region)
      const left = drawFormula(formula.left, { ...state, graph: scope.graph }, scope.value.left)
      return drawFormula(formula.right, left, scope.value.right)
    }
    case 'implies': {
      const scope = implication(state.graph, region)
      const antecedent = drawFormula(formula.left, { ...state, graph: scope.graph }, scope.value.antecedent)
      return drawFormula(formula.right, antecedent, scope.value.consequent)
    }
    case 'iff': {
      const scope = biconditional(state.graph, region)
      const forwardLeft = drawFormula(
        formula.left,
        { ...state, graph: scope.graph },
        scope.value.forward.antecedent,
      )
      const forwardRight = drawFormula(
        formula.right,
        forwardLeft,
        scope.value.forward.consequent,
      )
      const reverseRight = drawFormula(
        formula.right,
        forwardRight,
        scope.value.reverse.antecedent,
      )
      return drawFormula(formula.left, reverseRight, scope.value.reverse.consequent)
    }
    case 'quantifier': {
      const scope = quantifierScope(
        state.graph,
        region,
        formula.quantifier,
        formula.binders.map((binder) => binder.sig),
      )
      const bindings = new Map(state.bindings)
      formula.binders.forEach((binder, index) => {
        const wire = scope.value.variables[index]
        if (wire === undefined) throw new Error(`formula translation: missing wire for '${binder.name}'`)
        bindings.set(binder.name, wire)
      })
      const body = drawFormula(formula.body, { graph: scope.graph, bindings }, scope.value.body)
      return { graph: body.graph, bindings: state.bindings }
    }
  }
}

function formulaAstToDiagram(formula: Formula): Diagram {
  const graph = emptyGraph()
  return finishDiagram(drawFormula(formula, { graph, bindings: new Map() }, graph.root).graph)
}

/** Parse a formula source string and draw its authoritative diagram. */
export function formulaToDiagram(source: string): Diagram {
  return formulaAstToDiagram(parseFormula(source))
}
