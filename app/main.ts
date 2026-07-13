import { mountCursebreaker } from '../src/game'

const host = document.getElementById('cursebreaker')
if (!(host instanceof HTMLElement)) throw new Error("missing <main id='cursebreaker'>")

mountCursebreaker({ host })
