import { theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import type { BootContext } from '../../src/app/boot'
import { fetchBootContext } from '../../src/app/boot'

/**
 * The exact JSON the emit script ships, keyed by the URL fetchBootContext
 * requests. Passing this to fetchBootContext exercises the real boot path
 * (manifest → loadTheory per file → mergeTheories) with no HTTP or filesystem.
 */
export function inMemoryTheoryReader(): (url: string) => Promise<unknown> {
  const files = new Map<string, unknown>([
    ['theories/index.json', ['frege.json', 'lambda.json']],
    ['theories/frege.json', theoryToJson(buildFregeTheory())],
    ['theories/lambda.json', theoryToJson(buildLambdaTheory())],
  ])
  return (url) => {
    if (!files.has(url)) return Promise.reject(new Error(`no in-memory theory file at '${url}'`))
    return Promise.resolve(files.get(url))
  }
}

/** The merged boot context, loaded through the real verifying path. */
export function bootFixture(): Promise<BootContext> {
  return fetchBootContext(inMemoryTheoryReader())
}
