import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import { mountFormulaEntry } from '../../src/app/formula-entry'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { TestDocument, TestElement } from './helpers/fake-dom'

let documentDouble!: TestDocument

beforeEach(() => {
  documentDouble = new TestDocument()
  vi.stubGlobal('document', documentDouble)
})

afterEach(() => { vi.unstubAllGlobals() })

function mounted(commit: (diagram: Diagram) => void) {
  const host = documentDouble.createElement('main')
  const opener = documentDouble.createElement('button')
  host.append(opener)
  const entry = mountFormulaEntry(host as unknown as HTMLElement, commit)
  const textarea = entry.root.querySelector('textarea') as unknown as TestElement
  const form = entry.root.querySelector('form') as unknown as TestElement
  const error = entry.root.querySelector('.vpa-formula-error') as unknown as TestElement
  const symbols = entry.root.querySelector('.vpa-formula-symbols') as unknown as TestElement
  const actions = entry.root.querySelector('.vpa-formula-actions') as unknown as TestElement
  const cancel = actions.children[1] as TestElement
  return { entry, opener, textarea, form, error, symbols, cancel }
}

describe('mountFormulaEntry', () => {
  it('renders every supported Unicode symbol immediately below the source', () => {
    const { form, textarea, symbols } = mounted(vi.fn<(diagram: Diagram) => void>())

    expect(symbols.getAttribute('role')).toBe('group')
    expect(symbols.getAttribute('aria-label')).toBe('Formula symbols')
    expect(symbols.children.map((button) => button.textContent))
      .toEqual(['∀', '∃', '¬', '∧', '∨', '→', '⇒', '↔'])
    expect(symbols.children.every((button) => button.type === 'button')).toBe(true)
    expect(symbols.children.map((button) => button.getAttribute('aria-label'))).toEqual([
      'Universal quantifier',
      'Existential quantifier',
      'Negation',
      'Conjunction',
      'Disjunction',
      'Implication',
      'Alternative implication',
      'Biconditional',
    ])
    expect(form.children.indexOf(symbols)).toBe(form.children.indexOf(textarea) + 1)
  })

  it('replaces the textarea selection, advances the caret, restores focus, and clears errors', () => {
    const commit = vi.fn<(diagram: Diagram) => void>()
    const { entry, opener, textarea, form, error, symbols } = mounted(commit)
    entry.open(opener as unknown as HTMLElement)
    textarea.value = 'AB'
    form.dispatchEvent(new Event('submit', { cancelable: true }))
    expect(textarea.getAttribute('aria-invalid')).toBe('true')

    textarea.setSelectionRange(1, 1)
    symbols.children[4]!.dispatchEvent(new Event('click'))

    expect(textarea.value).toBe('A∨B')
    expect(textarea.selectionStart).toBe(2)
    expect(textarea.selectionEnd).toBe(2)
    expect(documentDouble.activeElement).toBe(textarea)
    expect(error.textContent).toBe('')
    expect(textarea.getAttribute('aria-invalid')).toBeNull()
  })

  it('commits a validated diagram and closes after a successful formula submission', () => {
    const commits: Diagram[] = []
    const { entry, opener, textarea, form } = mounted((diagram) => { commits.push(diagram) })

    entry.open(opener as unknown as HTMLElement)
    expect(documentDouble.activeElement).toBe(textarea)
    textarea.value = '∀ P : i → o. ∀ x : i. P(x)'
    form.dispatchEvent(new Event('submit', { cancelable: true }))

    expect(commits).toHaveLength(1)
    expect(Object.values(commits[0]!.nodes).filter((node) => node.kind === 'atom')).toHaveLength(1)
    expect(entry.root.hidden).toBe(true)
    expect(documentDouble.activeElement).toBe(opener)
  })

  it.each([
    ['Cancel', ({ cancel }: ReturnType<typeof mounted>) => cancel.dispatchEvent(new Event('click'))],
    ['Escape', ({ entry }: ReturnType<typeof mounted>) => {
      const event = new Event('keydown', { cancelable: true })
      Object.defineProperty(event, 'key', { value: 'Escape' })
      entry.root.dispatchEvent(event)
    }],
  ])('returns focus to the opener after %s', (_path, close) => {
    const { entry, opener, textarea, ...mountedEntry } = mounted(vi.fn<(diagram: Diagram) => void>())

    entry.open(opener as unknown as HTMLElement)
    expect(documentDouble.activeElement).toBe(textarea)
    close({ entry, opener, textarea, ...mountedEntry })

    expect(entry.root.hidden).toBe(true)
    expect(documentDouble.activeElement).toBe(opener)
  })

  it('does not resurrect opener focus on mode deactivation or disposal', () => {
    const { entry, opener, textarea } = mounted(vi.fn<(diagram: Diagram) => void>())

    entry.open(opener as unknown as HTMLElement)
    entry.deactivate()

    expect(opener.focusCalls).toBe(0)
    expect(documentDouble.activeElement).toBe(textarea)

    entry.open(opener as unknown as HTMLElement)
    entry.dispose()

    expect(opener.focusCalls).toBe(0)
  })

  it('keeps an invalid formula open, reports its location, and clears the field error on input', () => {
    const commit = vi.fn<(diagram: Diagram) => void>()
    const { entry, opener, textarea, form, error } = mounted(commit)

    entry.open(opener as unknown as HTMLElement)
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

  it('routes empty source through the formula parser rather than committing', () => {
    const commit = vi.fn<(diagram: Diagram) => void>()
    const { entry, opener, textarea, form, error } = mounted(commit)

    entry.open(opener as unknown as HTMLElement)
    form.dispatchEvent(new Event('submit', { cancelable: true }))

    expect(error.textContent).toMatch(/line 1, column \d+/u)
    expect(textarea.getAttribute('aria-invalid')).toBe('true')
    expect(entry.root.hidden).toBe(false)
    expect(commit).not.toHaveBeenCalled()
  })
})
