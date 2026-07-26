import { existsSync, readFileSync, readdirSync, statSync } from 'node:fs'
import { join } from 'node:path'
import * as ts from 'typescript'
import { describe, expect, it } from 'vitest'
import type { DiagramNode } from '../../src/kernel/diagram/diagram'

const nodeKinds = {
  atom: true,
  identity: true,
  ref: true,
} satisfies Record<DiagramNode['kind'], true>

const sortedNodeKinds = Object.keys(nodeKinds).sort()

const prohibitedSemanticSymbols = [
  "kind: 'term'",
  "kind: 'body'",
  'TermDiagramNode',
  'ConversionCertificate',
  'NormalSeparationCertificate',
  'applyFusion',
  'applyFission',
  'applyCongruenceJoin',
  'applyHeadStrip',
  'applyInconsistentCutElim',
  'applyBodyAttach',
  'applyBodyDetach',
  'relCongruenceJoin',
] as const

const removedRuleSymbols = prohibitedSemanticSymbols.slice(5)
const prohibitedIdentifiers = new Set([
  ...prohibitedSemanticSymbols.slice(2),
  'TERM',
])

const removedCodecRules = [
  'openTermSpawn',
  'relationSpawn',
  'boundRelationSpawn',
  'inconsistentCutElim',
  'conversion',
  'congruenceJoin',
  'anchoredWireSplit',
  'anchoredWireContract',
  'headStrip',
  'closedTermIntro',
  'fusion',
  'fission',
  'bodyAttach',
  'bodyDetach',
] as const

const negativeCodecFixture = 'tests/kernel/proof/json.test.ts'
const vocabularyGuard = 'tests/architecture/kernel-vocabulary.test.ts'

function tsFilesUnder(dir: string): string[] {
  const files: string[] = []
  for (const entry of readdirSync(dir)) {
    const path = join(dir, entry)
    if (statSync(path).isDirectory()) files.push(...tsFilesUnder(path))
    else if (entry.endsWith('.ts')) files.push(path)
  }
  return files.sort()
}

function parseTypeScript(file: string): ts.SourceFile {
  return ts.createSourceFile(
    file,
    readFileSync(file, 'utf8'),
    ts.ScriptTarget.Latest,
    true,
    ts.ScriptKind.TS,
  )
}

function propertyNameIsKind(name: ts.PropertyName | undefined): boolean {
  return name !== undefined
    && (
      (ts.isIdentifier(name) && name.text === 'kind')
      || (ts.isStringLiteral(name) && name.text === 'kind')
    )
}

function isKindAccess(node: ts.Node): boolean {
  return (
    ts.isPropertyAccessExpression(node)
    && node.name.text === 'kind'
  ) || (
    ts.isElementAccessExpression(node)
    && ts.isStringLiteral(node.argumentExpression)
    && node.argumentExpression.text === 'kind'
  )
}

function semanticKindLiteral(node: ts.StringLiteralLike): string | null {
  if (node.text !== 'term' && node.text !== 'body') return null
  const owner = ts.isLiteralTypeNode(node.parent) ? node.parent.parent : node.parent
  if (
    (ts.isPropertyAssignment(owner) || ts.isPropertySignature(owner))
    && propertyNameIsKind(owner.name)
  ) return `kind: '${node.text}'`
  if (
    ts.isBinaryExpression(owner)
    && (isKindAccess(owner.left) || isKindAccess(owner.right))
  ) return `kind comparison '${node.text}'`
  if (
    ts.isCaseClause(owner)
    && ts.isSwitchStatement(owner.parent.parent)
    && isKindAccess(owner.parent.parent.expression)
  ) return `kind case '${node.text}'`
  return null
}

function isTermModuleSpecifier(node: ts.StringLiteralLike): boolean {
  const parent = node.parent
  const moduleSpecifier = (
    ts.isImportDeclaration(parent)
    || ts.isExportDeclaration(parent)
  ) ? parent.moduleSpecifier : undefined
  return moduleSpecifier === node
    && /(^|\/)term($|\/)/.test(node.text.replace(/^\.+\//, ''))
}

function semanticOffenders(file: string, roots: readonly ts.Node[]): string[] {
  const offenders = new Set<string>()
  const visit = (node: ts.Node): void => {
    if (ts.isIdentifier(node) && prohibitedIdentifiers.has(node.text)) {
      offenders.add(`${file}: ${node.text}`)
    }
    if (ts.isStringLiteral(node) || ts.isNoSubstitutionTemplateLiteral(node)) {
      const kind = semanticKindLiteral(node)
      if (kind !== null) offenders.add(`${file}: ${kind}`)
      if (isTermModuleSpecifier(node)) offenders.add(`${file}: term module '${node.text}'`)
    }
    ts.forEachChild(node, visit)
  }
  for (const root of roots) visit(root)
  return [...offenders].sort()
}

function productionOffenders(): string[] {
  const offenders: string[] = []
  for (const file of tsFilesUnder('src')) {
    if (/(^|\/)term(?:\/|\.ts$)/.test(file)) offenders.push(`${file}: term module path`)
    const parsed = parseTypeScript(file)
    offenders.push(...semanticOffenders(file, parsed.statements))
  }
  return offenders.sort()
}

function hasExportModifier(statement: ts.Statement): boolean {
  return ts.canHaveModifiers(statement)
    && ts.getModifiers(statement)?.some((modifier) =>
      modifier.kind === ts.SyntaxKind.ExportKeyword
      || modifier.kind === ts.SyntaxKind.DefaultKeyword,
    ) === true
}

function testAuthorityStatements(file: string): { parsed: ts.SourceFile; statements: ts.Statement[] } {
  const parsed = parseTypeScript(file)
  const statements = parsed.statements
    .filter((statement) =>
      ts.isImportDeclaration(statement)
      || ts.isImportEqualsDeclaration(statement)
      || ts.isExportDeclaration(statement)
      || ts.isExportAssignment(statement)
      || hasExportModifier(statement),
    )
  return { parsed, statements }
}

function testAuthorityOffenders(): string[] {
  const offenders: string[] = []
  for (const file of tsFilesUnder('tests')) {
    const { statements } = testAuthorityStatements(file)
    offenders.push(...semanticOffenders(file, statements))
  }
  return offenders.sort()
}

function exactStringLiterals(file: string): string[] {
  const parsed = parseTypeScript(file)
  const literals: string[] = []
  const visit = (node: ts.Node): void => {
    if (ts.isStringLiteral(node) || ts.isNoSubstitutionTemplateLiteral(node)) {
      literals.push(node.text)
    }
    ts.forEachChild(node, visit)
  }
  visit(parsed)
  return literals
}

describe('Phase-1 kernel vocabulary conformance', () => {
  it('has exactly atom, ref, and identity diagram nodes', () => {
    expect(sortedNodeKinds).toEqual(['atom', 'identity', 'ref'])
  })

  it('physically removes both displaced term module trees', () => {
    expect(existsSync('src/kernel/term')).toBe(false)
    expect(existsSync('tests/kernel/term')).toBe(false)
  })

  it('keeps prohibited semantic symbols out of production TypeScript authority', () => {
    const offenders = productionOffenders()
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('keeps prohibited semantic symbols out of test imports and exports', () => {
    const offenders = testAuthorityOffenders()
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('retains removed rule names only as negative codec inputs', () => {
    const offenders: string[] = []
    for (const file of tsFilesUnder('tests')) {
      // Execution ruling: the guard must spell the displaced names it rejects;
      // the codec fixture may spell serialized names only to prove rejection.
      // Neither file is a live import/export or production authority.
      if (file === negativeCodecFixture || file === vocabularyGuard) continue
      const literals = new Set(exactStringLiterals(file))
      for (const rule of [...removedRuleSymbols, ...removedCodecRules]) {
        if (literals.has(rule)) offenders.push(`${file}: ${rule}`)
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })
})
