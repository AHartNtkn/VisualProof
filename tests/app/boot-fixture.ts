import { theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import type { BootContext } from '../../src/app/boot'
import type { Library } from '../../src/app/library'
import { mkLibrary, loadEntry, rebuild } from '../../src/app/library'

/**
 * The exact JSON the emit script ships, keyed by the URL the shell requests.
 * Passing this to fetchManifest exercises the real manifest read with no HTTP;
 * the library then loads each file through loadEntry (the same verifying road
 * the shell drives).
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

/**
 * A library with both shipped theories loaded — the explicit-load path a user
 * drives from the panel, built here through loadEntry so the fixture context is
 * whatever the real load produces.
 */
export function loadedLibraryFixture(): Library {
  let lib = mkLibrary(['frege.json', 'lambda.json'])
  lib = loadEntry(lib, 'frege.json', theoryToJson(buildFregeTheory()))
  lib = loadEntry(lib, 'lambda.json', theoryToJson(buildLambdaTheory()))
  return lib
}

/** The merged context of the fully-loaded library, via the real load+rebuild. */
export async function bootFixture(): Promise<BootContext> {
  return rebuild(loadedLibraryFixture())
}
