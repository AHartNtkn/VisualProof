import { expect, test as base, type Page } from '@playwright/test'
import { mkdtemp, rm, writeFile } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { theoryToJson } from '../src/kernel/proof/store'
import { tinyTheory } from '../tests/fixtures/zero-signature'

export type TheoryFiles = {
  readonly tiny: string
  readonly invalid: string
}

export const test = base.extend<{ theoryFiles: TheoryFiles }>({
  theoryFiles: async ({}, use) => {
    const directory = await mkdtemp(join(tmpdir(), 'vpa-e2e-theory-'))
    const files = {
      tiny: join(directory, 'zero-signature.json'),
      invalid: join(directory, 'invalid.json'),
    }
    await writeFile(files.tiny, JSON.stringify(theoryToJson(tinyTheory())))
    await writeFile(files.invalid, '{"relations":')
    try {
      await use(files)
    } finally {
      await rm(directory, { recursive: true, force: true })
    }
  },
})

export { expect }

export async function loadTinyTheory(page: Page, files: TheoryFiles): Promise<void> {
  await page.locator('#open-file-input').setInputFiles(files.tiny)
  await expect(page.locator('#library').getByRole('button', {
    name: 'Unload zero-signature.json',
    exact: true,
  })).toBeVisible()
}
