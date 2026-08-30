import type { TutorialInstruction } from '../src/game/tutorial'

export type TutorialCardController = {
  render(instruction: TutorialInstruction | null, enabled: boolean, developerMode: boolean): void
}

export type TutorialCardActions = {
  readonly edit: (milestoneId: TutorialInstruction['milestoneId']) => void
}

export function mountTutorialCard(
  root: HTMLElement,
  actions: TutorialCardActions,
): TutorialCardController {
  const figure = root.ownerDocument.createElement('div')
  figure.className = 'tutorial-companion'
  figure.dataset['tutorialFigure'] = ''
  figure.ariaHidden = 'true'

  for (const part of ['head', 'body', 'arms', 'legs'] as const) {
    const element = root.ownerDocument.createElement('span')
    element.className = `tutorial-companion-${part}`
    figure.appendChild(element)
  }

  const copy = root.ownerDocument.createElement('p')
  copy.className = 'tutorial-instruction'
  copy.dataset['tutorialInstruction'] = ''
  root.replaceChildren(figure, copy)
  let editableMilestone: TutorialInstruction['milestoneId'] | null = null

  root.addEventListener('click', () => {
    if (editableMilestone !== null) actions.edit(editableMilestone)
  })

  return {
    render(instruction, enabled, developerMode) {
      copy.textContent = instruction?.text ?? ''
      root.hidden = !enabled || instruction === null
      const visible = enabled && instruction !== null
      editableMilestone = visible && developerMode ? instruction.milestoneId : null
      if (!visible) delete root.dataset['tutorialMilestone']
      else root.dataset['tutorialMilestone'] = instruction.milestoneId
      if (editableMilestone === null) {
        delete root.dataset['tutorialEditable']
        root.removeAttribute('role')
        root.removeAttribute('aria-label')
        root.tabIndex = -1
      } else {
        root.dataset['tutorialEditable'] = 'true'
        root.setAttribute('role', 'button')
        root.setAttribute('aria-label', `Edit tutorial text for ${editableMilestone}`)
        root.tabIndex = 0
      }
    },
  }
}
