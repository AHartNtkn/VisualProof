export class FakeStyle {
  private readonly properties = new Map<string, string>()

  setProperty(name: string, value: string): void { this.properties.set(name, value) }
  getPropertyValue(name: string): string { return this.properties.get(name) ?? '' }
  removeProperty(name: string): string {
    const previous = this.getPropertyValue(name)
    this.properties.delete(name)
    return previous
  }
}

export class FakeClassList {
  constructor(private readonly element: FakeElement) {}

  add(...names: string[]): void {
    const values = new Set(this.element.className.split(/\s+/).filter(Boolean))
    for (const name of names) values.add(name)
    this.element.className = [...values].join(' ')
  }

  remove(...names: string[]): void {
    const removed = new Set(names)
    this.element.className = this.element.className.split(/\s+/)
      .filter((name) => name !== '' && !removed.has(name)).join(' ')
  }

  contains(name: string): boolean {
    return this.element.className.split(/\s+/).includes(name)
  }

  toggle(name: string, force?: boolean): boolean {
    const enabled = force ?? !this.contains(name)
    if (enabled) this.add(name)
    else this.remove(name)
    return enabled
  }
}

export class FakeElement extends EventTarget {
  readonly children: FakeElement[] = []
  readonly style = new FakeStyle()
  readonly dataset: Record<string, string> = {}
  readonly classList = new FakeClassList(this)
  readonly capturedPointers = new Set<number>()
  className = ''
  textContent = ''
  src = ''
  alt = ''
  type = ''
  tabIndex = 0
  scrollTop = 0
  scrollHeight = 0
  clientHeight = 0
  parent: FakeElement | null = null
  private readonly attributes = new Map<string, string>()

  constructor(readonly ownerDocument: FakeDocument, readonly tagName = 'DIV') { super() }

  append(...children: FakeElement[]): void {
    for (const child of children) {
      child.parent = this
      this.children.push(child)
    }
  }

  replaceChildren(...children: FakeElement[]): void {
    for (const child of this.children) child.parent = null
    this.children.splice(0)
    this.append(...children)
  }

  remove(): void {
    if (this.parent === null) return
    const index = this.parent.children.indexOf(this)
    if (index >= 0) this.parent.children.splice(index, 1)
    this.parent = null
  }

  setAttribute(name: string, value: string): void { this.attributes.set(name, value) }
  getAttribute(name: string): string | null { return this.attributes.get(name) ?? null }
  removeAttribute(name: string): void { this.attributes.delete(name) }
  setPointerCapture(pointerId: number): void { this.capturedPointers.add(pointerId) }
  releasePointerCapture(pointerId: number): void { this.capturedPointers.delete(pointerId) }
  hasPointerCapture(pointerId: number): boolean { return this.capturedPointers.has(pointerId) }

  querySelectorAll<T extends FakeElement = FakeElement>(selector: string): T[] {
    return descendants(this).filter((element) => matches(element, selector)) as T[]
  }

  querySelector<T extends FakeElement = FakeElement>(selector: string): T | null {
    return this.querySelectorAll<T>(selector)[0] ?? null
  }
}

export class FakeDocument {
  createElement(tagName: string): FakeElement {
    return new FakeElement(this, tagName.toUpperCase())
  }
}

const descendants = (root: FakeElement): FakeElement[] => root.children.flatMap((child) => [
  child,
  ...descendants(child),
])

const matches = (element: FakeElement, selector: string): boolean => {
  if (selector.startsWith('.')) return element.classList.contains(selector.slice(1))
  const data = selector.match(/^\[data-([a-z-]+)="([^"]+)"\]$/)
  if (data !== null) {
    const key = data[1]!.replace(/-([a-z])/g, (_, letter: string) => letter.toUpperCase())
    return element.dataset[key] === data[2]
  }
  return element.tagName.toLowerCase() === selector.toLowerCase()
}

export const eventWith = <T extends Record<string, unknown>>(
  type: string,
  values: T,
): Event & T => {
  const event = new Event(type, { cancelable: true })
  for (const [name, value] of Object.entries(values)) {
    Object.defineProperty(event, name, { configurable: true, value })
  }
  return event as Event & T
}
