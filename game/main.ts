import './style.css'

const root = document.querySelector<HTMLElement>('[data-game]')!
root.innerHTML = '<section class="start"><h1>Orchard</h1><p>Desktop shell ready.</p></section>'
root.dataset['ready'] = 'true'
