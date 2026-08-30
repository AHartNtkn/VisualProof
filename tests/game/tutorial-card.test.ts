import { describe, expect, it } from 'vitest'
import { mountTutorialCard } from '../../game/tutorial-card'

class TestElement extends EventTarget {
  hidden = false
  textContent = ''
  className = ''
  tabIndex = -1
  readonly dataset: Record<string, string> = {}
  readonly children: TestElement[] = []
  readonly attributes = new Map<string, string>()

  constructor(readonly ownerDocument: TestDocument, readonly tagName = 'DIV') { super() }

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

  setAttribute(name: string, value: string): void {
    this.attributes.set(name, value)
  }

  removeAttribute(name: string): void {
    this.attributes.delete(name)
  }

  getAttribute(name: string): string | null {
    return this.attributes.get(name) ?? null
  }

  click(): void {
    this.dispatchEvent(new Event('click'))
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
  const edited: string[] = []
  return {
    root,
    edited,
    controller: mountTutorialCard(root as unknown as HTMLElement, {
      edit: (milestoneId) => { edited.push(milestoneId) },
    }),
  }
}

describe('tutorial card', () => {
  it('renders one instruction beside one provisional companion without progress UI', () => {
    // Catches the single-instruction surface growing a checklist or duplicate commentary.
    const card = harness()
    card.controller.render({ milestoneId: 'move', text: 'Freshly edited guidance.' }, true, false)

    const instruction = card.root.querySelector<HTMLElement>('[data-tutorial-instruction]')
    expect(card.root.hidden).toBe(false)
    expect(card.root.dataset['tutorialMilestone']).toBe('move')
    expect(instruction?.textContent).toBe('Freshly edited guidance.')
    expect(card.root.querySelector('[data-tutorial-figure]')).not.toBeNull()
    expect(card.root.querySelector('[data-tutorial-checklist]')).toBeNull()
    expect(card.root.querySelector('[data-tutorial-progress]')).toBeNull()
    expect(card.root.children).toHaveLength(2)
  })

  it('hides when tutorials are disabled or the visible sequence is complete', () => {
    // Catches stale guidance surviving a setting change or the first-order explanation boundary.
    const card = harness()
    card.controller.render({ milestoneId: 'move', text: 'Freshly edited guidance.' }, false, true)
    expect(card.root.hidden).toBe(true)
    expect(card.root.dataset['tutorialMilestone']).toBeUndefined()

    card.controller.render(null, true, true)
    expect(card.root.hidden).toBe(true)
    expect(card.root.dataset['tutorialMilestone']).toBeUndefined()
  })

  it('advertises and invokes editing only for a visible developer-mode instruction', () => {
    // Catches the card exposing permanent editing outside the application developer gate.
    const card = harness()
    card.controller.render({ milestoneId: 'move', text: 'Use W to move.' }, true, false)
    card.root.click()
    expect(card.edited).toEqual([])
    expect(card.root.dataset['tutorialEditable']).toBeUndefined()
    expect(card.root.getAttribute('role')).toBeNull()

    card.controller.render({ milestoneId: 'move', text: 'Use W to move.' }, true, true)
    expect(card.root.dataset['tutorialEditable']).toBe('true')
    expect(card.root.getAttribute('role')).toBe('button')
    expect(card.root.tabIndex).toBe(0)
    card.root.click()
    expect(card.edited).toEqual(['move'])

    card.controller.render(null, true, true)
    card.root.click()
    expect(card.edited).toEqual(['move'])
  })
})
