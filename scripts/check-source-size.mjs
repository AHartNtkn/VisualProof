import { readdirSync, readFileSync, statSync } from 'node:fs'
import { join, relative } from 'node:path'

const MAX_LINES = 3000
const EXCLUDED_DIRECTORIES = new Set([
  '.git',
  '.lake',
  'build',
  'coverage',
  'dist',
  'node_modules',
])

function physicalLineCount(text) {
  if (text.length === 0) return 0
  const newlineCount = (text.match(/\n/g) ?? []).length
  return newlineCount + (text.endsWith('\n') ? 0 : 1)
}

function maintainedTextFiles(root) {
  const files = []
  for (const entry of readdirSync(root)) {
    if (EXCLUDED_DIRECTORIES.has(entry)) continue
    const path = join(root, entry)
    const stat = statSync(path)
    if (stat.isDirectory()) {
      files.push(...maintainedTextFiles(path))
    } else {
      const contents = readFileSync(path)
      if (!contents.includes(0)) files.push({ path, contents: contents.toString('utf8') })
    }
  }
  return files
}

const violations = maintainedTextFiles(process.cwd())
  .map(file => ({
    path: relative(process.cwd(), file.path),
    lines: physicalLineCount(file.contents),
  }))
  .filter(file => file.lines > MAX_LINES)
  .sort((left, right) => right.lines - left.lines)

if (violations.length > 0) {
  process.stderr.write(
    `Maintained source files may not exceed ${MAX_LINES} physical lines:\n`,
  )
  for (const violation of violations) {
    process.stderr.write(`  ${violation.lines} ${violation.path}\n`)
  }
  process.exit(1)
}

process.stdout.write(
  `Size audit passed: no maintained text file exceeds ${MAX_LINES} lines.\n`,
)
