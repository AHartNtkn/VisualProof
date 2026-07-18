import { readFile } from 'node:fs/promises'
import path from 'node:path'
import { describe, expect, test } from 'vitest'

describe('desktop build and package contract', () => {
  test('pins Electron tooling and provides renderer, Electron, desktop, development, and Linux package scripts', async () => {
    const packageDocument = JSON.parse(await readFile('package.json', 'utf8'))

    expect(packageDocument.main).toBe('dist-electron/main.js')
    expect(packageDocument.devDependencies.electron).toBe('43.1.1')
    expect(packageDocument.devDependencies['electron-builder']).toBe('26.15.3')
    expect(packageDocument.scripts).toMatchObject({
      'build:renderer': expect.any(String),
      'build:electron': expect.any(String),
      'build:desktop': expect.any(String),
      'desktop:dev': expect.any(String),
      'package:linux:dir': expect.any(String),
      'package:linux': expect.any(String),
    })
    expect(packageDocument.scripts['build:desktop']).toMatch(/build:renderer.*build:electron/)
  })

  test('packages only the local desktop outputs as ASAR for Linux AppImage and deb', async () => {
    const packageDocument = JSON.parse(await readFile('package.json', 'utf8'))
    const build = packageDocument.build

    expect(build).toMatchObject({
      appId: expect.stringMatching(/^com\./),
      productName: 'Cursebreaker',
      asar: true,
      directories: { output: 'release' },
      files: expect.arrayContaining(['app/dist/**/*', 'dist-electron/**/*']),
      linux: { category: 'Game', target: ['AppImage', 'deb'] },
    })
    expect(build).not.toHaveProperty('win')
    expect(build).not.toHaveProperty('mac')
    expect(build.linux.target).toEqual(['AppImage', 'deb'])
  })

  test('renderer and game production sources have no Electron, Node, filesystem, or localStorage authority', async () => {
    const roots = ['src/app', 'src/view', 'src/game', 'app']
    const forbidden = [
      /from\s+['"]electron['"]/,
      /from\s+['"]node:/,
      /from\s+['"](?:fs|path|os|child_process)['"]/,
      /\brequire\s*\(\s*['"](?:electron|node:|fs|path|os|child_process)/,
      /\blocalStorage\b/,
    ]
    const { readdir } = await import('node:fs/promises')
    const sourceFiles: string[] = []
    const collect = async (directory: string): Promise<void> => {
      for (const entry of await readdir(directory, { withFileTypes: true })) {
        const target = path.join(directory, entry.name)
        if (entry.isDirectory()) {
          if (entry.name !== 'dist') await collect(target)
        } else if (/\.(?:ts|tsx|js|jsx)$/.test(entry.name)) {
          sourceFiles.push(target)
        }
      }
    }
    await Promise.all(roots.map(collect))

    for (const sourceFile of sourceFiles) {
      const source = await readFile(sourceFile, 'utf8')
      for (const pattern of forbidden) expect(source, `${sourceFile} matches ${pattern}`).not.toMatch(pattern)
    }
  })
})
