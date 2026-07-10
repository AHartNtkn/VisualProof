import { mountLayoutFrame } from './layout-frame'
import type { LibraryPrototypeVariant } from './library-prototype'

const pageFor: Readonly<Record<LibraryPrototypeVariant, string>> = { ledger: 'a', prism: 'b', shelf: 'c' }

export async function mountLibraryRound(host: HTMLElement, variant: LibraryPrototypeVariant): Promise<void> {
  await mountLayoutFrame(host, 'compass', 'porcelain', `/ui-lab/library-app.html?debug&library=${variant}`)
  host.dataset.libraryPrototype = variant
  const switcher = host.querySelector<HTMLElement>('.layout-demo-switch')
  if (switcher === null) throw new Error('the comparison switch is missing')
  switcher.setAttribute('aria-label', 'Compare Library variants')
  switcher.innerHTML = '<span>LIBRARY</span><a href="/ui-lab/round16-a.html" data-library-link="ledger">A</a><a href="/ui-lab/round16-b.html" data-library-link="prism">B</a><a href="/ui-lab/round16-c.html" data-library-link="shelf">C</a>'
  switcher.querySelector(`[data-library-link="${variant}"]`)?.classList.add('is-current')
  const subtitle = host.querySelector<HTMLElement>('.layout-surface-head small')
  if (subtitle !== null) subtitle.textContent = variant === 'ledger'
    ? 'Browse verified knowledge or manage sources'
    : variant === 'prism'
      ? 'Verified knowledge, with source status one route away'
      : 'Filter knowledge through the visible source shelf'
  host.querySelector<HTMLButtonElement>('.layout-library-button')?.click()
  document.title = `Library ${pageFor[variant].toUpperCase()} — ${variant}`
}
