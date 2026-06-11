import { describe, it, expect } from 'vitest'
import { readFileSync, readdirSync, statSync } from 'node:fs'
import { join } from 'node:path'

function tsFilesUnder(dir: string): string[] {
  const out: string[] = []
  for (const entry of readdirSync(dir)) {
    const full = join(dir, entry)
    if (statSync(full).isDirectory()) out.push(...tsFilesUnder(full))
    else if (entry.endsWith('.ts')) out.push(full)
  }
  return out
}

function importSpecifiers(file: string): string[] {
  const src = readFileSync(file, 'utf8')
  const specs: string[] = []
  const re = /from\s+['"]([^'"]+)['"]|import\s*\(\s*['"]([^'"]+)['"]\s*\)|import\s+['"]([^'"]+)['"]/g
  for (let m = re.exec(src); m !== null; m = re.exec(src)) {
    specs.push(m[1] ?? m[2] ?? m[3]!)
  }
  return specs
}

describe('layer separation (spec §4.2)', () => {
  it('the kernel never imports from the view or theories layers', () => {
    const offenders: string[] = []
    for (const file of tsFilesUnder('src/kernel')) {
      for (const spec of importSpecifiers(file)) {
        if (spec.includes('/view/') || spec.startsWith('../view') || spec.startsWith('../../view') || spec.includes('/theories/') || spec.startsWith('../theories')) {
          offenders.push(`${file} imports '${spec}'`)
        }
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('theories import the kernel only', () => {
    const offenders: string[] = []
    for (const file of tsFilesUnder('src/theories')) {
      for (const spec of importSpecifiers(file)) {
        if (spec.includes('/view/') || spec.startsWith('../view')) {
          offenders.push(`${file} imports '${spec}'`)
        }
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('only the canvas adapter touches the canvas API', () => {
    const offenders: string[] = []
    for (const file of tsFilesUnder('src')) {
      if (file.endsWith('view/canvas.ts')) continue
      if (readFileSync(file, 'utf8').includes('CanvasRenderingContext2D')) {
        offenders.push(file)
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('nothing below the app layer imports it', () => {
    const offenders: string[] = []
    for (const dir of ['src/kernel', 'src/view', 'src/theories']) {
      for (const file of tsFilesUnder(dir)) {
        for (const spec of importSpecifiers(file)) {
          if (spec.includes('/app/') || spec.startsWith('../app')) {
            offenders.push(`${file} imports '${spec}'`)
          }
        }
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })

  it('no src code imports node built-ins', () => {
    // the kernel is pure data + algorithms and the view runs in the browser:
    // any node: import anywhere under src is a leak
    const offenders: string[] = []
    for (const file of tsFilesUnder('src')) {
      for (const spec of importSpecifiers(file)) {
        if (spec.startsWith('node:')) offenders.push(`${file} imports '${spec}'`)
      }
    }
    expect(offenders, offenders.join('\n')).toEqual([])
  })
})
