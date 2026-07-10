import { installFeedbackPrototype, type FeedbackPrototypeVariant } from './feedback-prototype'
import { mountLayoutFrame } from './layout-frame'

const pageFor: Readonly<Record<FeedbackPrototypeVariant, string>> = { field: 'a', ribbon: 'b', chronicle: 'c' }

export async function mountFeedbackRound(host: HTMLElement, variant: FeedbackPrototypeVariant): Promise<void> {
  await mountLayoutFrame(
    host,
    'compass',
    'porcelain',
    `/ui-lab/feedback-app.html?debug&feedback=${variant}`,
    { mirrorFeedback: false },
  )
  host.dataset.feedbackPrototype = variant
  const frame = host.querySelector<HTMLIFrameElement>('.layout-app')
  if (frame === null) throw new Error('the actual app frame is missing')
  installFeedbackPrototype(host, frame, variant)

  const switcher = host.querySelector<HTMLElement>('.layout-demo-switch')
  if (switcher === null) throw new Error('the comparison switch is missing')
  switcher.setAttribute('aria-label', 'Compare feedback variants')
  switcher.innerHTML = '<span>FEEDBACK</span><a href="/ui-lab/round17-a.html" data-feedback-link="field">A</a><a href="/ui-lab/round17-b.html" data-feedback-link="ribbon">B</a><a href="/ui-lab/round17-c.html" data-feedback-link="chronicle">C</a>'
  switcher.querySelector(`[data-feedback-link="${variant}"]`)?.classList.add('is-current')
  document.title = `Feedback ${pageFor[variant].toUpperCase()} — ${variant}`
}
