import { mountDualFrontPrototype } from '../src/app/dual-front-prototype'

const host = document.getElementById('dual-root')
if (!(host instanceof HTMLElement)) throw new Error('dual-front host is missing')
mountDualFrontPrototype(host)
