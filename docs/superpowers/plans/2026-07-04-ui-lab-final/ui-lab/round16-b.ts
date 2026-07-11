import { mountLibraryRound } from './round16'
const host = document.getElementById('layout-root')
if (!(host instanceof HTMLElement)) throw new Error('layout host is missing')
void mountLibraryRound(host, 'prism')
