import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest'
import { mountGenerateEntry } from '../../src/app/generate-entry'
import { GENERATOR_FAMILIES } from '../../src/generate'
import { DEFAULT_SEARCH_FUEL } from '../../src/generate/search/search'
import { seededRng } from '../../src/generate/rng'
import type { Diagram } from '../../src/kernel/diagram/diagram'
import { TestDocument, TestElement } from './helpers/fake-dom'

let documentDouble!: TestDocument

beforeEach(() => {
  documentDouble = new TestDocument()
  vi.stubGlobal('document', documentDouble)
})

afterEach(() => { vi.unstubAllGlobals() })

function mounted(commit: (diagram: Diagram) => void, options?: { rng?: () => number }) {
  const host = documentDouble.createElement('main')
  const opener = documentDouble.createElement('button')
  host.append(opener)
  const entry = mountGenerateEntry(host as unknown as HTMLElement, commit, options)
  const form = entry.root.querySelector('form') as unknown as TestElement
  const select = entry.root.querySelector('select') as unknown as TestElement
  const knobsContainer = entry.root.querySelector('.vpa-generate-knobs') as unknown as TestElement
  const fuelInput = entry.root.querySelector('.vpa-generate-fuel') as unknown as TestElement
  const statement = entry.root.querySelector('.vpa-generate-statement') as unknown as TestElement
  const difficulty = entry.root.querySelector('.vpa-generate-difficulty') as unknown as TestElement
  const error = entry.root.querySelector('.vpa-formula-error') as unknown as TestElement
  const actions = entry.root.querySelector('.vpa-formula-actions') as unknown as TestElement
  const generateBtn = actions.children[0] as TestElement
  const createBtn = actions.children[1] as TestElement
  const cancelBtn = actions.children[2] as TestElement
  return {
    entry, opener, form, select, knobsContainer, fuelInput, statement, difficulty, error, actions,
    generateBtn, createBtn, cancelBtn,
  }
}

/** Finds the knob row labeled `label` and returns its input. Throws if the
 *  panel's currently rendered knobs don't include that label — the point is
 *  to find inputs the same accessible way (label association) the e2e will. */
function knobInput(knobsContainer: TestElement, label: string): TestElement {
  for (const row of knobsContainer.children) {
    const rowLabel = row.querySelector('label') as unknown as TestElement | null
    if (rowLabel?.textContent === label) return row.querySelector('input') as unknown as TestElement
  }
  throw new Error(`no knob input labeled '${label}'`)
}

describe('mountGenerateEntry', () => {
  it('renders a hidden dialog with the family select, first-family knob inputs, and search-fuel input', () => {
    const { entry, select, knobsContainer, fuelInput } = mounted(vi.fn<(diagram: Diagram) => void>())

    expect(entry.root.hidden).toBe(true)
    expect(entry.root.getAttribute('role')).toBe('dialog')
    expect(select.children.map((option) => option.textContent)).toEqual(GENERATOR_FAMILIES.map((f) => f.label))
    expect(select.children.map((option) => option.value)).toEqual(GENERATOR_FAMILIES.map((f) => f.id))

    const firstFamily = GENERATOR_FAMILIES[0]!
    expect(knobsContainer.children).toHaveLength(firstFamily.knobs.length)
    firstFamily.knobs.forEach((knob, index) => {
      const row = knobsContainer.children[index]!
      const label = row.querySelector('label') as unknown as TestElement
      const input = row.querySelector('input') as unknown as TestElement
      expect(label.textContent).toBe(knob.label)
      expect(label.htmlFor).toBe(input.id)
      if (knob.kind === 'flag') {
        expect(input.type).toBe('checkbox')
        expect(input.checked).toBe(knob.default === 1)
      } else {
        expect(input.type).toBe('number')
        expect(input.value).toBe(String(knob.default))
        expect(input.min).toBe(String(knob.min))
      }
    })

    expect(fuelInput.value).toBe(String(DEFAULT_SEARCH_FUEL))
  })

  it("re-renders the knob inputs to the selected family's knobs on change", () => {
    const { select, knobsContainer } = mounted(vi.fn<(diagram: Diagram) => void>())

    const walkFamily = GENERATOR_FAMILIES.find((f) => f.id === 'prop-walk')!
    select.value = 'prop-walk'
    select.dispatchEvent(new Event('change'))

    expect(knobsContainer.children).toHaveLength(walkFamily.knobs.length)
    walkFamily.knobs.forEach((knob, index) => {
      const row = knobsContainer.children[index]!
      const label = row.querySelector('label') as unknown as TestElement
      const input = row.querySelector('input') as unknown as TestElement
      expect(label.textContent).toBe(knob.label)
      if (knob.kind === 'flag') {
        expect(input.type).toBe('checkbox')
        expect(input.checked).toBe(knob.default === 1)
      } else {
        expect(input.value).toBe(String(knob.default))
        expect(input.min).toBe(String(knob.min))
      }
    })
  })

  it.each([
    ['Cancel', ({ cancelBtn }: ReturnType<typeof mounted>) => cancelBtn.dispatchEvent(new Event('click'))],
    ['Escape', ({ entry }: ReturnType<typeof mounted>) => {
      const event = new Event('keydown', { cancelable: true })
      Object.defineProperty(event, 'key', { value: 'Escape' })
      entry.root.dispatchEvent(event)
    }],
  ])('open() unhides and focuses; %s closes and restores opener focus', (_path, close) => {
    const mountedEntry = mounted(vi.fn<(diagram: Diagram) => void>())
    const { entry, opener, select } = mountedEntry

    entry.open(opener as unknown as HTMLElement)
    expect(entry.root.hidden).toBe(false)
    expect(documentDouble.activeElement).toBe(select)

    close(mountedEntry)

    expect(entry.root.hidden).toBe(true)
    expect(documentDouble.activeElement).toBe(opener)
  })

  it('close() restores opener focus; deactivate() and dispose() do not', () => {
    const { entry, opener } = mounted(vi.fn<(diagram: Diagram) => void>())

    entry.open(opener as unknown as HTMLElement)
    entry.close()
    expect(opener.focusCalls).toBe(1)
    expect(documentDouble.activeElement).toBe(opener)

    entry.open(opener as unknown as HTMLElement)
    entry.deactivate()
    expect(opener.focusCalls).toBe(1)
    expect(entry.root.hidden).toBe(true)

    entry.open(opener as unknown as HTMLElement)
    entry.dispose()
    expect(opener.focusCalls).toBe(1)
  })

  it(
    'Generate produces a statement and difficulty line; Create diagram commits and closes',
    () => {
      const commits: Diagram[] = []
      const { entry, opener, knobsContainer, statement, difficulty, createBtn, generateBtn } =
        mounted((diagram) => { commits.push(diagram) }, { rng: seededRng(1) })

      entry.open(opener as unknown as HTMLElement)
      knobInput(knobsContainer, 'Atoms').value = '1'
      knobInput(knobsContainer, 'Sample connectives').value = '6'
      knobInput(knobsContainer, 'Minimum core connectives').value = '2'
      generateBtn.dispatchEvent(new Event('click'))

      expect(statement.textContent.length).toBeGreaterThan(0)
      expect(statement.textContent.startsWith('∀')).toBe(true)
      expect(
        difficulty.textContent.includes('minimal proof:') || difficulty.textContent.includes('no proof within'),
      ).toBe(true)

      expect(createBtn.type).toBe('submit')
      const form = entry.root.querySelector('form') as unknown as TestElement
      form.dispatchEvent(new Event('submit', { cancelable: true }))

      expect(commits).toHaveLength(1)
      expect(Object.keys(commits[0]!.regions).length).toBeGreaterThan(0)
      expect(entry.root.hidden).toBe(true)
      expect(documentDouble.activeElement).toBe(opener)
    },
    10_000,
  )

  it("a flag knob's checked state reaches generate() as 1/0", () => {
    // Toggling 'Full deiteration normalization' on, at a small attempt cap,
    // must hit the honest attempt-cap error (the measured near-total
    // collapse — see prop-family.test.ts/walk-family.test.ts) rather than
    // the unknown-knob or invalid-value errors a flag value NOT reaching
    // generate() correctly would produce. This is the cheapest deterministic
    // way to observe the checkbox's `checked` state actually flowing through
    // readKnobs into generate(), without hunting for a lucky success seed.
    const { entry, opener, knobsContainer, error, generateBtn } =
      mounted(vi.fn<(diagram: Diagram) => void>(), { rng: seededRng(11) })

    entry.open(opener as unknown as HTMLElement)
    knobInput(knobsContainer, 'Sample connectives').value = '9'
    knobInput(knobsContainer, 'Minimum core connectives').value = '3'
    knobInput(knobsContainer, 'Attempt cap').value = '50'
    const flagInput = knobInput(knobsContainer, 'Full deiteration normalization')
    expect(flagInput.type).toBe('checkbox')
    expect(flagInput.checked).toBe(false)
    flagInput.checked = true
    generateBtn.dispatchEvent(new Event('click'))

    expect(error.textContent).toMatch(/50 attempts/)
  })

  it('Create diagram before any generation reports an error instead of committing', () => {
    const commit = vi.fn<(diagram: Diagram) => void>()
    const { entry, opener, error } = mounted(commit)

    entry.open(opener as unknown as HTMLElement)
    const form = entry.root.querySelector('form') as unknown as TestElement
    form.dispatchEvent(new Event('submit', { cancelable: true }))

    expect(commit).not.toHaveBeenCalled()
    expect(error.textContent.length).toBeGreaterThan(0)
    expect(entry.root.hidden).toBe(false)
  })

  it('an invalid knob value surfaces the readKnobs error in the alert output', () => {
    const commit = vi.fn<(diagram: Diagram) => void>()
    const { entry, opener, knobsContainer, error, generateBtn, statement, difficulty } = mounted(commit)

    entry.open(opener as unknown as HTMLElement)
    knobInput(knobsContainer, 'Atoms').value = '0'
    generateBtn.dispatchEvent(new Event('click'))

    expect(error.textContent).toMatch(/atoms/u)
    expect(commit).not.toHaveBeenCalled()
    expect(statement.textContent).toBe('')
    expect(difficulty.textContent).toBe('')
  })
})
