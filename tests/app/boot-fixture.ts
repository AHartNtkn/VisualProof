import { theoryToJson } from '../../src/kernel/proof/store'
import { buildFregeTheory } from '../../src/theories/frege'
import { buildLambdaTheory } from '../../src/theories/lambda'
import type { BootContext } from '../../src/app/boot'
import type { Library } from '../../src/app/library'
import { emptyLibrary, loadEntry, rebuild } from '../../src/app/library'

/**
 * A library with both example theories loaded — the explicit-open path a user
 * drives from the panel, built here through loadEntry so the fixture context is
 * whatever the real load produces. The app itself ships no manifest and fetches
 * nothing; this fixture just feeds the generators' JSON straight through the
 * verifying road.
 */
export function loadedLibraryFixture(): Library {
  let lib = emptyLibrary()
  lib = loadEntry(lib, 'frege.json', theoryToJson(buildFregeTheory()))
  lib = loadEntry(lib, 'lambda.json', theoryToJson(buildLambdaTheory()))
  return lib
}

/** The merged context of the fully-loaded library, via the real load+rebuild. */
export async function bootFixture(): Promise<BootContext> {
  return rebuild(loadedLibraryFixture())
}
