import { FORMULA_UNICODE_SYMBOLS } from '../formula/syntax'

export type MountedFormulaSymbolButtons = {
  readonly buttons: readonly HTMLButtonElement[]
  dispose(): void
}

/** Mount the shared formula alphabet and insert selected symbols at the source caret. */
export function mountFormulaSymbolButtons(
  container: HTMLElement,
  source: HTMLTextAreaElement,
): MountedFormulaSymbolButtons {
  container.setAttribute('role', 'group')
  container.setAttribute('aria-label', 'Formula symbols')
  const entries = FORMULA_UNICODE_SYMBOLS.map(({ symbol, label }) => {
    const button = container.ownerDocument.createElement('button')
    button.type = 'button'
    button.textContent = symbol
    button.setAttribute('aria-label', label)
    button.setAttribute('title', label)
    const insert = (): void => {
      const start = source.selectionStart
      const end = source.selectionEnd
      source.value = source.value.slice(0, start) + symbol + source.value.slice(end)
      const caret = start + symbol.length
      source.setSelectionRange(caret, caret)
      source.dispatchEvent(new Event('input', { bubbles: true }))
      source.focus()
    }
    button.addEventListener('click', insert)
    container.append(button)
    return { button, insert }
  })

  return {
    buttons: entries.map(({ button }) => button),
    dispose: () => {
      for (const { button, insert } of entries) {
        button.removeEventListener('click', insert)
        button.remove()
      }
    },
  }
}
