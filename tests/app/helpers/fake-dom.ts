export class TestElement extends EventTarget {
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
  min = ''
  step = ''
  required = false
  isConnected = true
  focusCalls = 0
  selectionStart = 0
  selectionEnd = 0

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

  replaceChildren(...nodes: TestElement[]): void {
    for (const child of this.children) child.parentElement = null
    this.children.length = 0
    this.append(...nodes)
  }

  focus(): void {
    this.focusCalls += 1
    this.ownerDocument.activeElement = this
  }

  setSelectionRange(start: number, end: number): void {
    this.selectionStart = start
    this.selectionEnd = end
  }

  matches(selector: string): boolean { return selector === ':disabled' && this.required }

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

export class TestDocument {
  activeElement: TestElement | null = null

  createElement(tagName: string): TestElement { return new TestElement(this, tagName) }
}
