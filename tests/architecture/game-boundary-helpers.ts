import { readdirSync, statSync } from 'node:fs'
import { dirname, join, resolve, sep } from 'node:path'
import * as ts from 'typescript'

const nonLiteralDynamicImport = '\u0000non-literal-dynamic-import'

export function tsFilesUnder(dir: string): string[] {
  const files: string[] = []
  for (const entry of readdirSync(dir).sort()) {
    const path = join(dir, entry)
    if (statSync(path).isDirectory()) files.push(...tsFilesUnder(path))
    else if (entry.endsWith('.ts') || entry.endsWith('.tsx')) files.push(path)
  }
  return files
}

export function importSpecifiers(file: string, source: string): string[] {
  const scriptKind = file.endsWith('.tsx') ? ts.ScriptKind.TSX : ts.ScriptKind.TS
  const sourceFile = ts.createSourceFile(file, source, ts.ScriptTarget.Latest, true, scriptKind)
  const specifiers: string[] = []

  const addStringLiteral = (node: ts.Node | undefined): void => {
    if (node !== undefined && ts.isStringLiteralLike(node)) specifiers.push(node.text)
  }

  const visit = (node: ts.Node): void => {
    if (ts.isImportDeclaration(node) || ts.isExportDeclaration(node)) {
      addStringLiteral(node.moduleSpecifier)
    } else if (ts.isCallExpression(node) && node.expression.kind === ts.SyntaxKind.ImportKeyword) {
      const specifier = node.arguments[0]
      specifiers.push(specifier !== undefined && ts.isStringLiteral(specifier)
        ? specifier.text
        : nonLiteralDynamicImport)
    } else if (ts.isImportEqualsDeclaration(node)
      && ts.isExternalModuleReference(node.moduleReference)) {
      addStringLiteral(node.moduleReference.expression)
    }
    ts.forEachChild(node, visit)
  }

  visit(sourceFile)
  return specifiers
}

const isWithin = (candidate: string, root: string): boolean => (
  candidate === root || candidate.startsWith(`${root}${sep}`)
)

function isForbiddenSpecifier(file: string, specifier: string): boolean {
  if (/^(?:node:)?fs(?:\/|$)/.test(specifier)) return true
  if (/^fsaccess(?:\/|$)/.test(specifier)) return true

  let candidate: string | undefined
  if (specifier.startsWith('.')) candidate = resolve(dirname(file), specifier)
  else if (specifier === 'src' || specifier.startsWith('src/')) candidate = resolve(specifier)
  if (candidate === undefined) return false

  return ['src/app', 'src/theories', 'src/fsaccess']
    .map((root) => resolve(root))
    .some((root) => isWithin(candidate, root))
}

export function gameBoundaryOffenders(file: string, source: string): string[] {
  return importSpecifiers(file, source)
    .flatMap((specifier) => {
      if (specifier === nonLiteralDynamicImport) return [`${file} has a non-literal dynamic import`]
      return isForbiddenSpecifier(resolve(file), specifier) ? [`${file} imports '${specifier}'`] : []
    })
}
