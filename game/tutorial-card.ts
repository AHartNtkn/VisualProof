import type { TutorialInstruction } from '../src/game/tutorial'

export type TutorialCardController = {
  render(instruction: TutorialInstruction | null, enabled: boolean): void
}

export function mountTutorialCard(root: HTMLElement): TutorialCardController {
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

  return {
    render(instruction, enabled) {
      copy.textContent = instruction?.text ?? ''
      root.hidden = !enabled || instruction === null
      if (!enabled || instruction === null) delete root.dataset['tutorialMilestone']
      else root.dataset['tutorialMilestone'] = instruction.milestoneId
    },
  }
}
