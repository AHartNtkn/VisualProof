import { mountComprehensionPrototype } from '../src/app/comprehension-prototype'

const host = document.getElementById('comprehension-root')
if (!(host instanceof HTMLElement)) throw new Error('comprehension host is missing')
mountComprehensionPrototype(host)
