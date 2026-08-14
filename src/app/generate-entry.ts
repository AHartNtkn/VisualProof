import { GENERATOR_FAMILIES, readKnobs, type GeneratedProblem, type GeneratorFamily } from '../generate'
import { DEFAULT_SEARCH_FUEL, minimalProofSearch, type SearchOutcome } from '../generate/search/search'
import { seededRng } from '../generate/rng'
import type { Diagram } from '../kernel/diagram/diagram'

export type MountedGenerateEntry = {
  readonly root: HTMLElement
  open(opener: HTMLElement): void
  close(): void
  deactivate(): void
  dispose(): void
}

const CLASS_LABELS: Readonly<Record<string, string>> = {
  spawn: 'insertion',
  iteration: 'iteration/deiteration',
  doubleCut: 'double cuts',
}

function freshCryptoRng(): () => number {
  const seedArray = new Uint32Array(1)
  crypto.getRandomValues(seedArray)
  return seededRng(seedArray[0]!)
}

function difficultyLine(outcome: SearchOutcome, walkUpperBound: number | undefined): string {
  if (outcome.status === 'solved') {
    const base = outcome.mode === 'deletion-only'
      ? `minimal proof: ${outcome.length} moves (deletions only)`
      : `minimal proof: ${outcome.length} moves`
    const requires = outcome.requires.length > 0
      ? ` · requires ${outcome.requires.map((c) => CLASS_LABELS[c] ?? c).join(', ')}`
      : ''
    return base + requires
  }
  const bound = walkUpperBound !== undefined ? ` · provable in ${walkUpperBound} walk actions` : ''
  return `no deletions-only proof · no proof within ${outcome.noProofWithin} moves (search fuel exhausted)${bound}`
}

/** Random-problem generation panel: samples a problem from a chosen
 *  generator family, searches for its minimal proof, and hands the result's
 *  diagram to its caller. Structurally mirrors mountFormulaEntry — same
 *  dialog/lifecycle boilerplate — with a family picker + knob inputs and a
 *  Generate/Create diagram split (generation is a preview step; only
 *  Create diagram commits). */
export function mountGenerateEntry(
  host: HTMLElement,
  commit: (diagram: Diagram) => void,
  options: { rng?: () => number } = {},
): MountedGenerateEntry {
  const document = host.ownerDocument
  const root = document.createElement('section')
  root.className = 'vpa-formula-entry'
  root.hidden = true
  root.setAttribute('role', 'dialog')
  root.setAttribute('aria-labelledby', 'generate-entry-title')

  const form = document.createElement('form')
  const title = document.createElement('h2')
  title.id = 'generate-entry-title'
  title.textContent = 'Generate a random problem'

  const familyLabel = document.createElement('label')
  familyLabel.htmlFor = 'generate-family'
  familyLabel.textContent = 'Family'
  const familySelect = document.createElement('select')
  familySelect.id = 'generate-family'
  for (const family of GENERATOR_FAMILIES) {
    const option = document.createElement('option')
    option.value = family.id
    option.textContent = family.label
    familySelect.append(option)
  }

  const knobsContainer = document.createElement('div')
  knobsContainer.className = 'vpa-generate-knobs'

  const fuelLabel = document.createElement('label')
  fuelLabel.htmlFor = 'generate-fuel'
  fuelLabel.textContent = 'Search fuel'
  const fuelInput = document.createElement('input')
  fuelInput.className = 'vpa-generate-fuel'
  fuelInput.type = 'number'
  fuelInput.id = 'generate-fuel'
  fuelInput.min = '1'
  fuelInput.step = '1'
  fuelInput.value = String(DEFAULT_SEARCH_FUEL)

  const result = document.createElement('div')
  result.className = 'vpa-generate-result'
  const statementOutput = document.createElement('p')
  statementOutput.className = 'vpa-generate-statement'
  const difficultyOutput = document.createElement('p')
  difficultyOutput.className = 'vpa-generate-difficulty'
  result.append(statementOutput, difficultyOutput)

  const error = document.createElement('output')
  error.className = 'vpa-formula-error'
  error.setAttribute('role', 'alert')

  const actions = document.createElement('div')
  actions.className = 'vpa-formula-actions'
  const generate = document.createElement('button')
  generate.type = 'button'
  generate.textContent = 'Generate'
  const create = document.createElement('button')
  create.className = 'vpa-control-primary'
  create.type = 'submit'
  create.textContent = 'Create diagram'
  const cancel = document.createElement('button')
  cancel.type = 'button'
  cancel.textContent = 'Cancel'
  actions.append(generate, create, cancel)

  form.append(title, familyLabel, familySelect, knobsContainer, fuelLabel, fuelInput, result, error, actions)
  root.append(form)
  host.append(root)

  const initialFamily = GENERATOR_FAMILIES[0]
  if (initialFamily === undefined) throw new Error('mountGenerateEntry: GENERATOR_FAMILIES is empty')
  let currentFamily: GeneratorFamily = initialFamily
  const knobInputs = new Map<string, HTMLInputElement>()
  let current: GeneratedProblem | null = null

  const clearResult = (): void => {
    current = null
    statementOutput.textContent = ''
    difficultyOutput.textContent = ''
  }

  const renderKnobs = (): void => {
    knobInputs.clear()
    const rows: HTMLElement[] = []
    for (const knob of currentFamily.knobs) {
      const wrap = document.createElement('div')
      wrap.className = 'vpa-generate-knob'
      const label = document.createElement('label')
      label.htmlFor = `generate-knob-${knob.id}`
      label.textContent = knob.label
      const input = document.createElement('input')
      input.id = `generate-knob-${knob.id}`
      if (knob.kind === 'flag') {
        input.type = 'checkbox'
        input.checked = knob.default === 1
      } else {
        input.type = 'number'
        input.min = String(knob.min)
        input.step = '1'
        input.value = String(knob.default)
      }
      wrap.append(label, input)
      rows.push(wrap)
      knobInputs.set(knob.id, input)
    }
    knobsContainer.replaceChildren(...rows)
  }
  renderKnobs()

  const onFamilyChange = (): void => {
    const next = GENERATOR_FAMILIES.find((family) => family.id === familySelect.value)
    if (next === undefined) throw new Error(`mountGenerateEntry: unknown family '${familySelect.value}'`)
    currentFamily = next
    renderKnobs()
    error.textContent = ''
    clearResult()
  }

  const onGenerate = (): void => {
    try {
      const params: Record<string, number> = {}
      for (const [id, input] of knobInputs) {
        const knob = currentFamily.knobs.find((candidate) => candidate.id === id)
        if (knob === undefined) throw new Error(`mountGenerateEntry: knob input '${id}' has no matching KnobSpec`)
        params[id] = knob.kind === 'flag' ? (input.checked ? 1 : 0) : Number(input.value)
      }
      const knobs = readKnobs(currentFamily, params)
      const rng = options.rng ?? freshCryptoRng()
      const problem = currentFamily.generate(knobs, rng)
      const outcome = minimalProofSearch(problem.diagram, Number(fuelInput.value))
      current = problem
      statementOutput.textContent = problem.statement
      difficultyOutput.textContent = difficultyLine(outcome, problem.walkUpperBound)
      error.textContent = ''
    } catch (caught) {
      clearResult()
      error.textContent = caught instanceof Error ? caught.message : String(caught)
    }
  }

  let opener: HTMLElement | null = null
  const hide = (restoreFocus: boolean): void => {
    root.hidden = true
    error.textContent = ''
    const focusTarget = opener
    opener = null
    if (restoreFocus && focusTarget !== null && focusTarget.isConnected && !focusTarget.hidden && !focusTarget.matches(':disabled')) {
      focusTarget.focus()
    }
  }
  const close = (): void => {
    hide(true)
  }
  const deactivate = (): void => {
    hide(false)
  }
  const open = (nextOpener: HTMLElement): void => {
    if (disposed) return
    opener = nextOpener
    root.hidden = false
    familySelect.focus()
  }
  const onCancel = (): void => close()
  const onKeyDown = (event: Event): void => {
    if ((event as KeyboardEvent).key !== 'Escape') return
    event.preventDefault()
    close()
  }
  const onSubmit = (event: Event): void => {
    event.preventDefault()
    if (current === null) {
      error.textContent = 'generate a problem first'
      return
    }
    commit(current.diagram)
    close()
  }
  familySelect.addEventListener('change', onFamilyChange)
  generate.addEventListener('click', onGenerate)
  cancel.addEventListener('click', onCancel)
  root.addEventListener('keydown', onKeyDown)
  form.addEventListener('submit', onSubmit)

  let disposed = false
  return {
    root,
    open,
    close,
    deactivate,
    dispose: (): void => {
      if (disposed) return
      disposed = true
      familySelect.removeEventListener('change', onFamilyChange)
      generate.removeEventListener('click', onGenerate)
      cancel.removeEventListener('click', onCancel)
      root.removeEventListener('keydown', onKeyDown)
      form.removeEventListener('submit', onSubmit)
      opener = null
      root.remove()
    },
  }
}
