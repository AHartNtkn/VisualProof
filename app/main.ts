import { mountShell } from '../src/app/index'

const canvas = document.getElementById('c')
const chrome = document.getElementById('chrome')
if (!(canvas instanceof HTMLCanvasElement)) throw new Error("missing <canvas id='c'> in app/index.html")
if (!(chrome instanceof HTMLElement)) throw new Error("missing <div id='chrome'> in app/index.html")

mountShell({ canvas, chrome })
