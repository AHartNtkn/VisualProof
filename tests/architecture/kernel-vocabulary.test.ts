import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  rmSync,
  statSync,
  unlinkSync,
  writeFileSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
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
  'isExactReificationDefinition',
])

const removedCodecRules = [
  'openTermSpawn',
  'relationSpawn',
  'boundRelationSpawn',
  'inconsistentCutElim',
  'conversion',
  'congruenceJoin',
  'identityContradiction',
  'anchoredWireSplit',
  'anchoredWireContract',
  'headStrip',
  'closedTermIntro',
  'fusion',
  'fission',
  'bodyAttach',
  'bodyDetach',
] as const

const prohibitedAuthorityStrings = new Set<string>([
  ...prohibitedIdentifiers,
  ...removedCodecRules,
])
const removedTestRuleLiterals = new Set<string>([
  ...removedRuleSymbols,
  ...removedCodecRules,
])

const negativeCodecFixture = 'tests/kernel/proof/json.test.ts'
const vocabularyGuard = 'tests/architecture/kernel-vocabulary.test.ts'
const leanSemanticsGuard = 'tests/architecture/lean-semantics.test.ts'

const absentAuthorityPaths = [
  'src/kernel/diagram/canonical/shape.ts',
  'src/kernel/diagram/canonical/matchkey.ts',
  'src/kernel/rules/anchored-wire.ts',
  'src/kernel/rules/body.ts',
  'src/kernel/rules/congruence.ts',
  'src/kernel/rules/conversion.ts',
  'src/kernel/rules/fusion.ts',
  'src/kernel/rules/headstrip.ts',
  'src/kernel/rules/inconsistent-cut.ts',
  'src/kernel/rules/intro.ts',
  'src/kernel/rules/port-correspondence.ts',
  'src/kernel/rules/reification.ts',
  'src/kernel/term',
  'tests/kernel/term',
  'tests/kernel/rules/anchored-wire.test.ts',
  'tests/kernel/rules/body.test.ts',
  'tests/kernel/rules/congruence.test.ts',
  'tests/kernel/rules/conversion.test.ts',
  'tests/kernel/rules/fusion.test.ts',
  'tests/kernel/rules/headstrip.test.ts',
  'tests/kernel/rules/inconsistent-cut.test.ts',
  'tests/kernel/rules/intro.test.ts',
  'tests/kernel/rules/port-correspondence.test.ts',
  'tests/kernel/rules/uniqueness-representability.test.ts',
  'tests/kernel/formal/correspondence.test.ts',
  'tests/kernel/formal/highlevel-alias-parity.test.ts',
  'src/app/abstraction-matches.ts',
  'src/app/tactics.ts',
  'src/app/relation-transactions.ts',
  'src/app/relation-workspace.ts',
  'src/app/relation-workspace-draft.ts',
  'src/app/interact/closed-term-intro.ts',
  'src/app/interact/comprehension-macros.ts',
  'src/app/interact/fission.ts',
  'src/interaction/named-relation.ts',
  'tests/app/abstraction-interaction.test.ts',
  'tests/app/abstraction-matches.test.ts',
  'tests/app/closed-term-intro.test.ts',
  'tests/app/comprehension-macros.test.ts',
  'tests/app/fission-interaction.test.ts',
  'tests/app/relation-transactions.test.ts',
  'tests/app/relation-workspace-dependencies.test.ts',
  'tests/app/relation-workspace-draft.test.ts',
  'tests/app/relation-workspace.test.ts',
  'tests/app/tactics.test.ts',
  'tests/interaction/named-relation.test.ts',
  'app/test/relation-workspace.html',
  'app/test/relation-workspace.ts',
  'e2e/abstraction.spec.ts',
  'e2e/relation-workspace.spec.ts',
  'src/view/tromp.ts',
  'tests/view/tromp.test.ts',
  'src/theories/lambda.ts',
  'src/theories/macros.ts',
  'tests/theories/battery.test.ts',
  'tests/theories/lambda.test.ts',
  'tests/theories/macros.test.ts',
  'examples/lambda.json',
] as const

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
      if (prohibitedAuthorityStrings.has(node.text)) {
        offenders.add(`${file}: string authority '${node.text}'`)
      }
    }
    ts.forEachChild(node, visit)
  }
  for (const root of roots) visit(root)
  return [...offenders].sort()
}

function productionOffenders(
  roots: readonly string[] = ['src', 'scripts'],
): string[] {
  const offenders: string[] = []
  for (const root of roots) {
    for (const file of tsFilesUnder(root)) {
      if (/(^|\/)term(?:\/|\.ts$)/.test(file)) offenders.push(`${file}: term module path`)
      const parsed = parseTypeScript(file)
      offenders.push(...semanticOffenders(file, parsed.statements))
    }
  }
  return offenders.sort()
}

function absentPathOffenders(paths: readonly string[]): string[] {
  return paths.filter((path) => existsSync(path)).sort()
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

function exactStringLiteralNodes(parsed: ts.SourceFile): ts.StringLiteralLike[] {
  const literals: ts.StringLiteralLike[] = []
  const visit = (node: ts.Node): void => {
    if (ts.isStringLiteral(node) || ts.isNoSubstitutionTemplateLiteral(node)) {
      literals.push(node)
    }
    ts.forEachChild(node, visit)
  }
  visit(parsed)
  return literals
}

function literalSpan(node: ts.StringLiteralLike): string {
  return `${node.pos}:${node.end}`
}

function importsNamed(
  parsed: ts.SourceFile,
  moduleSpecifier: string,
  importedName: string,
): boolean {
  return parsed.statements.some((statement) => {
    if (
      !ts.isImportDeclaration(statement)
      || !ts.isStringLiteral(statement.moduleSpecifier)
      || statement.moduleSpecifier.text !== moduleSpecifier
    ) return false
    const bindings = statement.importClause?.namedBindings
    return bindings !== undefined
      && ts.isNamedImports(bindings)
      && bindings.elements.some((element) =>
        (element.propertyName?.text ?? element.name.text) === importedName
        && element.name.text === importedName,
      )
  })
}

function callNamed(node: ts.Node, name: string): node is ts.CallExpression {
  return ts.isCallExpression(node)
    && ts.isIdentifier(node.expression)
    && node.expression.text === name
}

function decoderCallUsesRule(node: ts.Node, variable: string): boolean {
  if (!callNamed(node, 'stepFromJson')) return false
  const argument = node.arguments[0]
  if (argument === undefined || !ts.isObjectLiteralExpression(argument)) return false
  return argument.properties.some((property) =>
    (
      ts.isShorthandPropertyAssignment(property)
      && property.name.text === variable
    ) || (
      ts.isPropertyAssignment(property)
      && (
        (ts.isIdentifier(property.name) && property.name.text === 'rule')
        || (ts.isStringLiteral(property.name) && property.name.text === 'rule')
      )
      && ts.isIdentifier(property.initializer)
      && property.initializer.text === variable
    ),
  )
}

function loopExecutesDecoderRejection(
  parsed: ts.SourceFile,
  loop: ts.ForOfStatement,
  variable: string,
): boolean {
  const statement = ts.isBlock(loop.statement)
    && loop.statement.statements.length === 1
    ? loop.statement.statements[0]
    : loop.statement
  if (
    statement === undefined
    || !ts.isExpressionStatement(statement)
    || !ts.isCallExpression(statement.expression)
    || !ts.isPropertyAccessExpression(statement.expression.expression)
    || statement.expression.expression.name.text !== 'toThrow'
  ) return false
  const expectCall = statement.expression.expression.expression
  if (!callNamed(expectCall, 'expect')) return false
  const thunk = expectCall.arguments[0]
  const matcher = statement.expression.arguments[0]
  return thunk !== undefined
    && ts.isArrowFunction(thunk)
    && !ts.isBlock(thunk.body)
    && decoderCallUsesRule(thunk.body, variable)
    && matcher !== undefined
    && matcher.getText(parsed) === '/unknown rule/'
}

function bindingNameDeclares(binding: ts.BindingName, name: string): boolean {
  if (ts.isIdentifier(binding)) return binding.text === name
  return binding.elements.some((element) =>
    !ts.isOmittedExpression(element)
    && bindingNameDeclares(element.name, name),
  )
}

function declaresValueName(parsed: ts.SourceFile, name: string): boolean {
  let found = false
  const visit = (node: ts.Node): void => {
    if (found) return
    if (
      (ts.isVariableDeclaration(node) || ts.isParameter(node))
      && bindingNameDeclares(node.name, name)
    ) {
      found = true
      return
    }
    const directName = (
      ts.isFunctionDeclaration(node)
      || ts.isFunctionExpression(node)
      || ts.isClassDeclaration(node)
      || ts.isClassExpression(node)
      || ts.isEnumDeclaration(node)
    ) ? node.name : undefined
    if (directName !== undefined && directName.text === name) {
      found = true
      return
    }
    ts.forEachChild(node, visit)
  }
  visit(parsed)
  return found
}

function decoderRejectionEvidence(): {
  readonly permitted: ReadonlySet<string>
  readonly errors: readonly string[]
} {
  const parsed = parseTypeScript(negativeCodecFixture)
  const errors: string[] = []
  if (!importsNamed(parsed, 'vitest', 'it') || !importsNamed(parsed, 'vitest', 'expect')) {
    errors.push(`${negativeCodecFixture}: rejection test must import it and expect from vitest`)
  }
  if (!importsNamed(parsed, '../../../src/kernel/proof/json', 'stepFromJson')) {
    errors.push(`${negativeCodecFixture}: rejection test must import the production stepFromJson`)
  }
  for (const importedName of ['it', 'expect', 'stepFromJson']) {
    if (declaresValueName(parsed, importedName)) {
      errors.push(`${negativeCodecFixture}: rejection authority shadows imported ${importedName}`)
    }
  }

  const rejectionTests: ts.CallExpression[] = []
  const findTest = (node: ts.Node): void => {
    if (callNamed(node, 'it')) {
      const title = node.arguments[0]
      if (
        title !== undefined
        && ts.isStringLiteral(title)
        && title.text === 'rejects every removed proof-rule string'
      ) rejectionTests.push(node)
    }
    ts.forEachChild(node, findTest)
  }
  findTest(parsed)
  if (rejectionTests.length !== 1) {
    errors.push(`${negativeCodecFixture}: expected one exact removed-rule rejection test`)
    return { permitted: new Set(), errors }
  }

  const callback = rejectionTests[0]!.arguments[1]
  if (
    callback === undefined
    || (!ts.isArrowFunction(callback) && !ts.isFunctionExpression(callback))
  ) {
    errors.push(`${negativeCodecFixture}: removed-rule rejection test needs an executable callback`)
    return { permitted: new Set(), errors }
  }

  const loops: ts.ForOfStatement[] = []
  const findLoop = (node: ts.Node): void => {
    if (ts.isForOfStatement(node) && ts.isVariableDeclarationList(node.initializer)) {
      const declaration = node.initializer.declarations[0]
      if (
        node.initializer.declarations.length === 1
        && declaration !== undefined
        && ts.isIdentifier(declaration.name)
        && declaration.name.text === 'rule'
        && ts.isArrayLiteralExpression(node.expression)
      ) loops.push(node)
    }
    ts.forEachChild(node, findLoop)
  }
  findLoop(callback.body)
  if (loops.length !== 1) {
    errors.push(`${negativeCodecFixture}: expected one for-of rejection loop over rule`)
    return { permitted: new Set(), errors }
  }

  const loop = loops[0]!
  const array = loop.expression as ts.ArrayLiteralExpression
  const elements = array.elements.filter(ts.isStringLiteral)
  const actual = elements.map((element) => element.text)
  if (
    elements.length !== array.elements.length
    || JSON.stringify(actual) !== JSON.stringify(removedCodecRules)
  ) {
    errors.push(`${negativeCodecFixture}: rejection loop must enumerate exactly every removed codec rule`)
  }
  if (!loopExecutesDecoderRejection(parsed, loop, 'rule')) {
    errors.push(`${negativeCodecFixture}: rejection loop must assert stepFromJson({ rule }) throws /unknown rule/`)
  }
  return { permitted: new Set(elements.map(literalSpan)), errors }
}

describe('Phase-1 kernel vocabulary conformance', () => {
  it('has exactly atom, ref, and identity diagram nodes', () => {
    expect(sortedNodeKinds).toEqual(['atom', 'identity', 'ref'])
  })

  it('physically removes every displaced Phase-1 authority', () => {
    expect(absentPathOffenders(absentAuthorityPaths)).toEqual([])
  })

  it('keeps prohibited semantic symbols out of src and executable script authority', () => {
    const offenders = productionOffenders()
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('detects and clears a legacy authority mutation under executable scripts', () => {
    const scratch = mkdtempSync(join(tmpdir(), 'vpa-kernel-vocabulary-'))
    const script = join(scratch, 'scripts', 'legacy.ts')
    mkdirSync(dirname(script), { recursive: true })
    try {
      writeFileSync(script, 'export function applyFusion(): void {};\n')
      expect(productionOffenders([join(scratch, 'scripts')])).toContain(
        `${script}: applyFusion`,
      )

      writeFileSync(script, "export const nodeKind = 'identity';\n")
      expect(productionOffenders([join(scratch, 'scripts')])).toEqual([])
    } finally {
      rmSync(scratch, { recursive: true, force: true })
    }
  })

  it('detects and clears a resurrected absent-path mutation', () => {
    const scratch = mkdtempSync(join(tmpdir(), 'vpa-kernel-absence-'))
    const resurrected = join(scratch, 'src', 'kernel', 'rules', 'fusion.ts')
    mkdirSync(dirname(resurrected), { recursive: true })
    try {
      writeFileSync(resurrected, 'export {}\n')
      expect(absentPathOffenders([resurrected])).toEqual([resurrected])

      unlinkSync(resurrected)
      expect(absentPathOffenders([resurrected])).toEqual([])
    } finally {
      rmSync(scratch, { recursive: true, force: true })
    }
  })

  it('keeps prohibited semantic symbols out of test imports and exports', () => {
    const offenders = testAuthorityOffenders()
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('retains removed rule names only as negative codec inputs', () => {
    const evidence = decoderRejectionEvidence()
    const offenders = [...evidence.errors]
    for (const file of tsFilesUnder('tests')) {
      // Execution ruling: the guard must spell the displaced names it rejects;
      // those declarations are test machinery, not application authority. The
      // Lean-semantics guard spells them for the same reason: its literals are
      // negative not-toContain assertions over Lean sources.
      if (file === vocabularyGuard || file === leanSemanticsGuard) continue
      const parsed = parseTypeScript(file)
      for (const literal of exactStringLiteralNodes(parsed)) {
        if (
          !removedTestRuleLiterals.has(literal.text)
          || (
            file === negativeCodecFixture
            && evidence.permitted.has(literalSpan(literal))
          )
        ) continue
        offenders.push(`${file}: ${literal.text}`)
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })
})
