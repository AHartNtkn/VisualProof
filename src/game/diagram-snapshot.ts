import type { Diagram } from '../kernel/diagram'
import { diagramFromJson, diagramToJson } from '../kernel/diagram'

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
    return new DiagramSnapshot(diagram, JSON.stringify(diagramToJson(diagram)))
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
