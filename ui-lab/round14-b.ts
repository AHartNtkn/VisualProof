import { mountLayoutFrame } from './layout-frame'

const host = document.getElementById('layout-root')
if (!(host instanceof HTMLElement)) throw new Error('layout host is missing')
void mountLayoutFrame(host, 'phase')
