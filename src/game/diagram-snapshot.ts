import type { Diagram } from '../kernel/diagram'
import { diagramFromJson, diagramToJson } from '../kernel/diagram'

function freezeOwned<Value>(value: Value, seen = new WeakSet<object>()): Value {
  if (typeof value !== 'object' || value === null || seen.has(value)) return value
  seen.add(value)
  for (const child of Object.values(value)) freezeOwned(child, seen)
  return Object.freeze(value)
}

export class DiagramSnapshot {
  readonly #brand = true

  private constructor(
    public readonly diagram: Diagram,
    public readonly json: string,
  ) {
    void this.#brand
    Object.freeze(this)
  }

  public static fromDiagram(diagram: Diagram): DiagramSnapshot {
    const json = JSON.stringify(diagramToJson(diagram))
    const owned = freezeOwned(diagramFromJson(JSON.parse(json)))
    return new DiagramSnapshot(owned, json)
  }

  public static fromJson(json: string): DiagramSnapshot {
    let parsed: unknown
    try {
      parsed = JSON.parse(json)
    } catch (error) {
      throw new Error(
        `malformed diagram JSON: ${error instanceof Error ? error.message : String(error)}`,
      )
    }
    return DiagramSnapshot.fromDiagram(diagramFromJson(parsed))
  }
}

export function snapshotFromDiagram(diagram: Diagram): DiagramSnapshot {
  return DiagramSnapshot.fromDiagram(diagram)
}

export function snapshotFromJson(json: string): DiagramSnapshot {
  return DiagramSnapshot.fromJson(json)
}
