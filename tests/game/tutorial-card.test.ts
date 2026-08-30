import { describe, expect, it } from 'vitest'
import { mountTutorialCard } from '../../game/tutorial-card'

class TestElement {
  hidden = false
  textContent = ''
  className = ''
  readonly dataset: Record<string, string> = {}
  readonly children: TestElement[] = []

  constructor(readonly ownerDocument: TestDocument, readonly tagName = 'DIV') {}

  append(...children: TestElement[]): void {
    this.children.push(...children)
  }

  appendChild(child: TestElement): TestElement {
    this.children.push(child)
    return child
  }

  replaceChildren(...children: TestElement[]): void {
    this.children.splice(0, this.children.length, ...children)
  }

  querySelector<T extends Element>(selector: string): T | null {
    const key = selector.match(/^\[data-([a-z0-9-]+)\]$/)?.[1]
    if (key === undefined) throw new Error(`unsupported selector '${selector}'`)
    const datasetKey = key.replace(/-([a-z])/g, (_whole, letter: string) => letter.toUpperCase())
    if (Object.hasOwn(this.dataset, datasetKey)) return this as unknown as T
    for (const child of this.children) {
      const found = child.querySelector<T>(selector)
      if (found !== null) return found
    }
    return null
  }
}

class TestDocument {
  createElement(tagName: string): TestElement {
    return new TestElement(this, tagName.toUpperCase())
  }
}

function harness() {
  const documentTarget = new TestDocument()
  const root = new TestElement(documentTarget)
  return { root, controller: mountTutorialCard(root as unknown as HTMLElement) }
}

describe('tutorial card', () => {
  it('renders one instruction beside one provisional companion without progress UI', () => {
    // Catches the single-instruction surface growing a checklist or duplicate commentary.
    const card = harness()
    card.controller.render({ milestoneId: 'move', text: 'Move through the orchard.' }, true)

    const instruction = card.root.querySelector<HTMLElement>('[data-tutorial-instruction]')
    expect(card.root.hidden).toBe(false)
    expect(instruction?.textContent).toBe('Move through the orchard.')
    expect(card.root.querySelector('[data-tutorial-figure]')).not.toBeNull()
    expect(card.root.querySelector('[data-tutorial-checklist]')).toBeNull()
    expect(card.root.querySelector('[data-tutorial-progress]')).toBeNull()
    expect(card.root.children).toHaveLength(2)
  })

  it('hides when tutorials are disabled or the visible sequence is complete', () => {
    // Catches stale guidance surviving a setting change or the first-order explanation boundary.
    const card = harness()
    card.controller.render({ milestoneId: 'move', text: 'Move through the orchard.' }, false)
    expect(card.root.hidden).toBe(true)

    card.controller.render(null, true)
    expect(card.root.hidden).toBe(true)
  })
})
