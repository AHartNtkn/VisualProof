import { TOOL_CATALOG, type ToolId, type ToolInventory } from '../src/game/tools'

export type ToolSelectorController = {
  render(inventory: ToolInventory, now: number): void
  clear(): void
}

function definitionFor(id: ToolId) {
  const definition = TOOL_CATALOG.find((candidate) => candidate.id === id)
  if (definition === undefined) throw new Error(`unknown tool '${id}'`)
  return definition
}

function applyToolMetadata(element: HTMLElement, toolId: ToolId): void {
  const definition = definitionFor(toolId)
  element.dataset['toolId'] = definition.id
  element.dataset['silhouette'] = definition.silhouette
  element.style.setProperty('--tool-color', definition.color)
}

export function mountToolSelector(root: HTMLElement): ToolSelectorController {
  return {
    render(inventory, now) {
      const selection = inventory.selectorAt(now)
      if (selection === null) {
        root.replaceChildren()
        return
      }

      const category = root.ownerDocument.createElement('kbd')
      category.className = 'tool-selector-category'
      category.textContent = selection.category
      const list = root.ownerDocument.createElement('div')
      list.className = 'tool-selector-list'
      for (const toolId of selection.acquired) {
        const definition = definitionFor(toolId)
        const row = root.ownerDocument.createElement('div')
        row.className = 'tool-selector-row tool-silhouette'
        row.dataset['selected'] = String(toolId === selection.selected)
        applyToolMetadata(row, toolId)
        row.textContent = definition.label
        list.append(row)
      }
      root.replaceChildren(category, list)
    },
    clear() {
      root.replaceChildren()
    },
  }
}

export function renderHeldToolModel(root: HTMLElement, toolId: ToolId, cuttingHeld: boolean): void {
  const silhouette = root.querySelector<HTMLElement>('[data-held-tool-silhouette]')
  if (silhouette === null) throw new Error("missing held tool element '[data-held-tool-silhouette]'")
  applyToolMetadata(silhouette, toolId)
  root.dataset['cuttingHeld'] = String(cuttingHeld)
}
