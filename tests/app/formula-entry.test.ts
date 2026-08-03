import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import { mountFormulaEntry } from '../../src/app/formula-entry'
import type { Diagram } from '../../src/kernel/diagram/diagram'

class TestElement extends EventTarget {
  readonly children: TestElement[] = []
  readonly attributes = new Map<string, string>()
  readonly ownerDocument: TestDocument
  parentElement: TestElement | null = null
  className = ''
  textContent = ''
  hidden = false
  value = ''
  type = ''
  id = ''
  htmlFor = ''
  required = false

  constructor(ownerDocument: TestDocument, readonly tagName: string) {
    super()
    this.ownerDocument = ownerDocument
  }

  append(...nodes: TestElement[]): void {
    for (const node of nodes) {
      node.parentElement = this
      this.children.push(node)
    }
  }

  remove(): void {
    if (this.parentElement === null) return
    const index = this.parentElement.children.indexOf(this)
    if (index >= 0) this.parentElement.children.splice(index, 1)
    this.parentElement = null
  }

  focus(): void {}

  setAttribute(name: string, value: string): void { this.attributes.set(name, value) }
  getAttribute(name: string): string | null { return this.attributes.get(name) ?? null }
  removeAttribute(name: string): void { this.attributes.delete(name) }

  querySelector(selector: string): TestElement | null {
    const matches = (element: TestElement): boolean => selector.startsWith('.')
      ? element.className.split(/\s+/u).includes(selector.slice(1))
      : element.tagName === selector.toLowerCase()
    for (const child of this.children) {
      if (matches(child)) return child
      const nested = child.querySelector(selector)
      if (nested !== null) return nested
    }
    return null
  }
}

class TestDocument {
  createElement(tagName: string): TestElement { return new TestElement(this, tagName) }
}

let documentDouble!: TestDocument

beforeEach(() => {
  documentDouble = new TestDocument()
  vi.stubGlobal('document', documentDouble)
})

afterEach(() => { vi.unstubAllGlobals() })

function mounted(commit: (diagram: Diagram) => void) {
  const host = documentDouble.createElement('main')
  const entry = mountFormulaEntry(host as unknown as HTMLElement, commit)
  const textarea = entry.root.querySelector('textarea') as unknown as TestElement
  const form = entry.root.querySelector('form') as unknown as TestElement
  const error = entry.root.querySelector('.vpa-formula-error') as unknown as TestElement
  return { entry, textarea, form, error }
}

describe('mountFormulaEntry', () => {
  it('commits a validated diagram and closes after a successful formula submission', () => {
    const commits: Diagram[] = []
    const { entry, textarea, form } = mounted((diagram) => { commits.push(diagram) })

    entry.open()
    textarea.value = '∀ P : i → o. ∀ x : i. P(x)'
    form.dispatchEvent(new Event('submit', { cancelable: true }))

    expect(commits).toHaveLength(1)
    expect(Object.values(commits[0]!.nodes).filter((node) => node.kind === 'atom')).toHaveLength(1)
    expect(entry.root.hidden).toBe(true)
  })

  it('keeps an invalid formula open, reports its location, and clears the field error on input', () => {
    const commit = vi.fn<(diagram: Diagram) => void>()
    const { entry, textarea, form, error } = mounted(commit)

    entry.open()
    textarea.value = '∀ x. Missing(x)'
    form.dispatchEvent(new Event('submit', { cancelable: true }))

    expect(error.textContent).toMatch(/line 1, column \d+/u)
    expect(textarea.getAttribute('aria-invalid')).toBe('true')
    expect(entry.root.hidden).toBe(false)
    expect(commit).not.toHaveBeenCalled()

    textarea.dispatchEvent(new Event('input'))

    expect(error.textContent).toBe('')
    expect(textarea.getAttribute('aria-invalid')).toBeNull()
  })
})
