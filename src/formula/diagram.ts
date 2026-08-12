import type { Diagram, RegionId, WireId } from '../kernel/diagram/diagram'
import {
  atom,
  emptyGraph,
  finishDiagram,
  identity,
  implication,
  quantifierScope,
  type GraphConstruction,
} from '../theories/graph'
import { parseFormula } from './parse'
import type { Formula } from './syntax'

type TranslationState = {
  readonly graph: GraphConstruction
  readonly bindings: ReadonlyMap<string, WireId>
}

function boundWire(bindings: ReadonlyMap<string, WireId>, name: string): WireId {
  const wire = bindings.get(name)
  if (wire === undefined) throw new Error(`formula translation: unbound name '${name}'`)
  return wire
}

function drawFormula(
  formula: Formula,
  state: TranslationState,
  region: RegionId,
): TranslationState {
  switch (formula.kind) {
    case 'atom': {
      const relation = boundWire(state.bindings, formula.name)
      const args = formula.args.map((name) => boundWire(state.bindings, name))
      return { ...state, graph: atom(state.graph, region, relation, args).graph }
    }
    case 'equality': {
      const wires = formula.operands.map((name) => boundWire(state.bindings, name))
      return { ...state, graph: identity(state.graph, region, wires).graph }
    }
    case 'and':
      return drawFormula(formula.right, drawFormula(formula.left, state, region), region)
    case 'implies': {
      const scope = implication(state.graph, region)
      const antecedent = drawFormula(formula.left, { ...state, graph: scope.graph }, scope.value.antecedent)
      return drawFormula(formula.right, antecedent, scope.value.consequent)
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
