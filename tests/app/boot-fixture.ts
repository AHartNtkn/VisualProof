import type { BootContext } from '../../src/app/boot'
import type { Library } from '../../src/app/library'
import { emptyLibrary, loadEntry, rebuild } from '../../src/app/library'
import { theoryToJson } from '../../src/kernel/proof/store'
import { tinyTheory } from '../fixtures/zero-signature'

export function loadedLibraryFixture(): Library {
  return loadEntry(emptyLibrary(), 'tiny.json', theoryToJson(tinyTheory()))
}

export async function bootFixture(): Promise<BootContext> {
  return rebuild(loadedLibraryFixture())
}
