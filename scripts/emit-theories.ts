import { writeFileSync } from 'node:fs'
import { theoryToJson } from '../src/kernel/proof/store'
import { buildFregeTheory } from '../src/theories'

const output = `${JSON.stringify(theoryToJson(buildFregeTheory()), null, 2)}\n`

writeFileSync('examples/frege.json', output, 'utf8')
