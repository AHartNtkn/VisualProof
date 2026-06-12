// Smoke: kernel imports + convertible() facts needed by plusComm design.
// Constants are opaque to convertible(); test with unfolded forms.
import { parseTerm } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/parse'
import { convertible } from '/home/ahart/Documents/VisualProofAssistant/src/kernel/term/convert'

const Z = '(\\f.\\x.x)'
const S = '(\\n.\\f.\\x. f (n f x))'
const P = '(\\m.\\n.\\f.\\x. m f (n f x))'
const p = (s: string) => parseTerm(s, new Set<string>())
const conv = (a: string, b: string): string => convertible(p(a), p(b), 8192).status
console.log('units:', conv(`${P} ${Z} q_0`, `${P} q_0 ${Z}`))
console.log('left-shift applied:', conv(`${P} (${S} q) q_0`, `${S} (${P} q q_0)`))
console.log('comm-must-fail:', conv(`${P} q q_0`, `${P} q_0 q`))
