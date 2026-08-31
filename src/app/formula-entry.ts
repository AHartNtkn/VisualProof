import { formulaToDiagram } from '../formula'
import type { Diagram } from '../kernel/diagram/diagram'
import { mountFormulaSymbolButtons } from '../ui/formula-symbol-buttons'

export type MountedFormulaEntry = {
  readonly root: HTMLElement
  open(opener: HTMLElement): void
  close(): void
  deactivate(): void
  dispose(): void
}

/** Focused source entry that translates formulas before handing diagrams to its caller. */
export function mountFormulaEntry(host: HTMLElement, commit: (diagram: Diagram) => void): MountedFormulaEntry {
  const document = host.ownerDocument
  const root = document.createElement('section')
  root.className = 'vpa-formula-entry'
  root.hidden = true
  root.setAttribute('role', 'dialog')
  root.setAttribute('aria-labelledby', 'formula-entry-title')

  const form = document.createElement('form')
  const title = document.createElement('h2')
  title.id = 'formula-entry-title'
  title.textContent = 'Formula to diagram'
  const label = document.createElement('label')
  label.htmlFor = 'formula-entry-source'
  label.textContent = 'Formula to diagram'
  const textarea = document.createElement('textarea')
  textarea.id = 'formula-entry-source'
  textarea.setAttribute('aria-label', 'Formula to diagram')
  const symbols = document.createElement('div')
  symbols.className = 'vpa-formula-symbols'
  const symbolButtons = mountFormulaSymbolButtons(symbols, textarea)
  const error = document.createElement('output')
  error.className = 'vpa-formula-error'
  error.setAttribute('role', 'alert')
  const actions = document.createElement('div')
  actions.className = 'vpa-formula-actions'
  const create = document.createElement('button')
  create.className = 'vpa-control-primary'
  create.type = 'submit'
  create.textContent = 'Create diagram'
  const cancel = document.createElement('button')
  cancel.type = 'button'
  cancel.textContent = 'Cancel'
  actions.append(create, cancel)
  form.append(title, label, textarea, symbols, error, actions)
  root.append(form)
  host.append(root)

  const clearError = (): void => {
    error.textContent = ''
    textarea.removeAttribute('aria-invalid')
  }
  let opener: HTMLElement | null = null
  const hide = (restoreFocus: boolean): void => {
    root.hidden = true
    clearError()
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
    textarea.focus()
  }
  const onInput = (): void => clearError()
  const onCancel = (): void => close()
  const onKeyDown = (event: Event): void => {
    if ((event as KeyboardEvent).key !== 'Escape') return
    event.preventDefault()
    close()
  }
  const onSubmit = (event: Event): void => {
    event.preventDefault()
    try {
      const diagram = formulaToDiagram(textarea.value)
      commit(diagram)
      close()
    } catch (caught) {
      error.textContent = caught instanceof Error ? caught.message : String(caught)
      textarea.setAttribute('aria-invalid', 'true')
    }
  }
  textarea.addEventListener('input', onInput)
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
      textarea.removeEventListener('input', onInput)
      cancel.removeEventListener('click', onCancel)
      symbolButtons.dispose()
      root.removeEventListener('keydown', onKeyDown)
      form.removeEventListener('submit', onSubmit)
      opener = null
      root.remove()
    },
  }
}
