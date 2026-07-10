import { mountLayoutFrame } from './layout-frame'

export async function mountFeedbackRound(host: HTMLElement): Promise<void> {
  await mountLayoutFrame(
    host,
    'aperture',
    'porcelain',
    '/ui-lab/feedback-app.html?debug',
  )
  host.dataset.feedbackModel = 'error-only'

  const switcher = host.querySelector<HTMLElement>('.layout-demo-switch')
  if (switcher === null) throw new Error('the comparison switch is missing')
  switcher.setAttribute('aria-label', 'Approved feedback model')
  switcher.innerHTML = '<span>FEEDBACK · APPROVED</span>'
  document.title = 'Error-only feedback — approved'
}
