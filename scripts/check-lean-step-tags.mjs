import { readFileSync } from 'node:fs'
import { spawnSync } from 'node:child_process'

function fail(message) {
  process.stderr.write(`${message}\n`)
  process.exit(1)
}

function duplicates(values) {
  const seen = new Set()
  const repeated = new Set()
  for (const value of values) {
    if (seen.has(value)) repeated.add(value)
    seen.add(value)
  }
  return [...repeated].sort()
}

const emitted = spawnSync('lake', ['exe', 'visualproof_step_tags'], {
  cwd: process.cwd(),
  encoding: 'utf8',
})
if (emitted.status !== 0) {
  fail(`lake exe visualproof_step_tags failed\n${emitted.stdout}${emitted.stderr}`)
}

const jsonLine = emitted.stdout.split(/\r?\n/).map(line => line.trim())
  .findLast(line => line.startsWith('[') && line.endsWith(']'))
if (jsonLine === undefined) fail('Lean step-tag emitter produced no JSON array')

let leanTags
try {
  leanTags = JSON.parse(jsonLine)
} catch (error) {
  fail(`Lean step-tag emitter produced invalid JSON: ${String(error)}`)
}
if (!Array.isArray(leanTags) || leanTags.some(tag => typeof tag !== 'string')) {
  fail('Lean step-tag emitter JSON must be an array of strings')
}

const source = readFileSync('src/kernel/proof/step.ts', 'utf8')
const unionStart = source.indexOf('export type ProofStep =')
const unionEnd = source.indexOf('export function applyStep', unionStart)
if (unionStart < 0 || unionEnd < 0) {
  fail('Could not locate the TypeScript ProofStep union')
}
const proofStepUnion = source.slice(unionStart, unionEnd)
const tsTags = [...proofStepUnion.matchAll(/readonly\s+rule:\s*'([^']+)'/g)]
  .map(match => match[1])

const leanDuplicates = duplicates(leanTags)
const tsDuplicates = duplicates(tsTags)
const leanSet = new Set(leanTags)
const tsSet = new Set(tsTags)
const missingFromTypeScript = [...leanSet].filter(tag => !tsSet.has(tag)).sort()
const missingFromLean = [...tsSet].filter(tag => !leanSet.has(tag)).sort()

if (leanDuplicates.length || tsDuplicates.length ||
    missingFromTypeScript.length || missingFromLean.length) {
  fail([
    'Lean/TypeScript proof-step correspondence failed',
    `duplicate Lean tags: ${JSON.stringify(leanDuplicates)}`,
    `duplicate TypeScript tags: ${JSON.stringify(tsDuplicates)}`,
    `missing from TypeScript: ${JSON.stringify(missingFromTypeScript)}`,
    `missing from Lean: ${JSON.stringify(missingFromLean)}`,
  ].join('\n'))
}

process.stdout.write(`Lean and TypeScript agree on ${leanSet.size} proof-step tags.\n`)
