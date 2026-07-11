import type { Library } from '../src/app/library'
import { adoptEntry, defineEntry, emptyLibrary, loadEntry, reconcile } from '../src/app/library'
import type { DiagramWithBoundary } from '../src/kernel/diagram/boundary'
import type { Theorem } from '../src/kernel/proof/theorem'
import { loadTheory, theoryToJson } from '../src/kernel/proof/store'

export type LibraryFixture = {
  readonly library: Library
  readonly directory: FileSystemDirectoryHandle
  readonly errors: ReadonlyMap<string, string>
  readonly diagram: DiagramWithBoundary
}

const fetchSource = async (url: string): Promise<string> => {
  const response = await fetch(url)
  if (!response.ok) throw new Error(`failed to load '${url}' (${response.status})`)
  return response.text()
}

export async function loadLibraryFixture(): Promise<LibraryFixture> {
  const [fregeSource, lambdaSource] = await Promise.all([
    fetchSource('/examples/frege.json'),
    fetchSource('/examples/lambda.json'),
  ])
  const frege = loadTheory(JSON.parse(fregeSource)).theory

  let library = emptyLibrary()
  library = loadEntry(library, 'frege.json', JSON.parse(fregeSource))
  library = loadEntry(library, 'lambda.json', JSON.parse(lambdaSource))
  library = reconcile(library, ['frege.json', 'lambda.json', 'available.json', 'broken.json'])

  const zero = frege.relations.zero
  if (zero === undefined) throw new Error("the verified Library fixture has no 'zero' relation")
  library = defineEntry(library, 'sessionZero', zero)
  const basis = frege.theorems.find((theorem) => theorem.name === 'plusAssoc')
  if (basis === undefined) throw new Error("the verified Library fixture has no 'plusAssoc' theorem")
  const sessionTheorem: Theorem = { name: 'sessionIdentity', lhs: basis.lhs, rhs: basis.lhs, steps: [] }
  library = adoptEntry(library, sessionTheorem)

  const availableSource = JSON.stringify(theoryToJson({ relations: { availableZero: zero }, theorems: [] }))
  const directorySources = new Map([
    ['frege.json', fregeSource],
    ['lambda.json', lambdaSource],
    ['available.json', availableSource],
    ['broken.json', '{"format":"not-a-visual-proof-theory"}'],
  ])
  const directory = {
    kind: 'directory',
    name: 'Proof sources',
    async *values(): AsyncGenerator<FileSystemHandle> {
      for (const name of directorySources.keys()) yield { kind: 'file', name } as FileSystemFileHandle
    },
    async getFileHandle(name: string): Promise<FileSystemFileHandle> {
      const source = directorySources.get(name)
      if (source === undefined) throw new DOMException(`no file '${name}'`, 'NotFoundError')
      return {
        kind: 'file',
        name,
        getFile: async () => new File([source], name, { type: 'application/json' }),
      } as FileSystemFileHandle
    },
  } as FileSystemDirectoryHandle

  const errors = new Map<string, string>()
  try {
    loadEntry(library, 'broken.json', { format: 'not-a-visual-proof-theory' })
  } catch (error) {
    errors.set('broken.json', error instanceof Error ? error.message : String(error))
  }
  const diagram = frege.relations.nat
  if (diagram === undefined) throw new Error("the verified Library fixture has no 'nat' relation")
  return { library, directory, errors, diagram }
}
