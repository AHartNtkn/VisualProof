import { chromium, type Browser } from '@playwright/test'
import { resolve } from 'node:path'
import { afterEach, describe, expect, it } from 'vitest'
import { createServer, type ViteDevServer } from 'vite'
import { mountToolSelector, renderHeldToolModel } from '../../game/tool-selector'
import { TOOL_CATALOG, ToolInventory } from '../../src/game/tools'
import {
  decodeToolContent,
  LiveToolContent,
  openingToolContent,
} from '../../src/game/tools/content'

const repositoryRoot = resolve(import.meta.dirname, '../..')
let browser: Browser | undefined
let server: ViteDevServer | undefined

afterEach(async () => {
  await browser?.close()
  browser = undefined
  await server?.close()
  server = undefined
})

class TestElement {
  public textContent = ''
  public className = ''
  public readonly dataset: Record<string, string> = {}
  public readonly children: TestElement[] = []
  public readonly style = {
    values: new Map<string, string>(),
    setProperty: (name: string, value: string): void => { this.style.values.set(name, value) },
  }

  public constructor(public readonly ownerDocument: TestDocument) {}

  public append(...children: TestElement[]): void {
    this.children.push(...children)
  }

  public replaceChildren(...children: TestElement[]): void {
    this.children.splice(0, this.children.length, ...children)
  }

  public querySelector<T extends Element>(selector: string): T | null {
    const key = selector.match(/^\[data-([a-z0-9-]+)\]$/)?.[1]
    if (key === undefined) throw new Error(`unsupported selector '${selector}'`)
    const datasetKey = key.replace(/-([a-z])/g, (_whole, letter: string) => letter.toUpperCase())
    if (Object.hasOwn(this.dataset, datasetKey)) return this as unknown as T
    for (const child of this.children) {
      const found = child.querySelector<T>(selector)
      if (found !== null) return found
    }
    return null
  }
}

class TestDocument {
  public createElement(): TestElement {
    return new TestElement(this)
  }
}

function descendants(root: TestElement): readonly TestElement[] {
  return root.children.flatMap((child) => [child, ...descendants(child)])
}

describe('temporary tool selector', () => {
  it('resolves labels from the current live tool content on every render', () => {
    // Catches a mounted selector retaining copy from before a successful permanent publication.
    const documentTarget = new TestDocument()
    const root = documentTarget.createElement()
    const live = new LiveToolContent(openingToolContent.current)
    const inventory = new ToolInventory(new Set(['sprout-spawner', 'double-cut', 'iteration']), () => 100)
    const selector = mountToolSelector(root as unknown as HTMLElement, () => live.current)
    inventory.cycle('1', 100)
    live.publish(decodeToolContent(live.current.definitions.map((definition) => ({
      ...definition,
      name: definition.id === 'double-cut' ? 'Published selector copy' : definition.name,
    }))))

    selector.render(inventory, 100)

    const selected = descendants(root).find(({ dataset }) => dataset['selected'] === 'true')
    expect(selected?.textContent).toBe('Published selector copy')
  })
  it('is empty when expired and otherwise shows the category and every acquired label once', () => {
    // Catches a permanent selected-tool HUD or acquired tools disappearing from the temporary reveal.
    const documentTarget = new TestDocument()
    const root = documentTarget.createElement()
    const content = decodeToolContent(openingToolContent.current.definitions.map((definition) => ({
      ...definition,
      name: `Selector ${definition.id}`,
      description: `Description for ${definition.id}.`,
    })))
    const inventory = new ToolInventory(new Set(['sprout-spawner', 'double-cut', 'iteration']), () => 100)
    const selector = mountToolSelector(root as unknown as HTMLElement, () => content)
    inventory.cycle('1', 100)

    selector.render(inventory, 101)
    const rows = descendants(root).filter(({ dataset }) => Object.hasOwn(dataset, 'toolId'))
    expect(root.children[0]?.textContent).toBe('1')
    expect(rows.map(({ textContent }) => textContent)).toEqual([
      'Selector sprout-spawner',
      'Selector double-cut',
      'Selector iteration',
    ])
    expect(rows.filter(({ dataset }) => dataset['selected'] === 'true')).toHaveLength(1)
    expect(rows.find(({ dataset }) => dataset['selected'] === 'true')?.dataset['toolId']).toBe('double-cut')

    selector.render(inventory, 1900)
    expect(root.children).toHaveLength(0)
  })

  it('keeps selector rows and held models synchronized with distinct authored presentations', () => {
    // Mutation caught: either surface substitutes its own presentation or two tools become indistinguishable.
    const documentTarget = new TestDocument()
    const selectorRoot = documentTarget.createElement()
    const heldRoot = documentTarget.createElement()
    const heldSilhouette = documentTarget.createElement()
    heldSilhouette.dataset['heldToolSilhouette'] = ''
    heldRoot.append(heldSilhouette)
    const inventory = new ToolInventory(new Set(['sprout-spawner', 'double-cut', 'iteration']), () => 100)
    inventory.cycle('1', 100)

    mountToolSelector(selectorRoot as unknown as HTMLElement).render(inventory, 101)
    const rows = descendants(selectorRoot).filter(({ dataset }) => Object.hasOwn(dataset, 'toolId'))
    const rendered = rows.map(({ dataset, style }) => ({
      id: dataset['toolId'], silhouette: dataset['silhouette'], color: style.values.get('--tool-color'),
    }))
    expect(rendered).toEqual(TOOL_CATALOG.map(({ id, silhouette, color }) => ({ id, silhouette, color })))
    expect(new Set(rendered.map(({ silhouette }) => silhouette))).toHaveLength(TOOL_CATALOG.length)
    expect(new Set(rendered.map(({ color }) => color))).toHaveLength(TOOL_CATALOG.length)

    renderHeldToolModel(heldRoot as unknown as HTMLElement, 'iteration', true)
    const selected = TOOL_CATALOG.find(({ id }) => id === 'iteration')!
    expect(heldSilhouette.dataset).toMatchObject({
      toolId: selected.id,
      silhouette: selected.silhouette,
    })
    expect(heldSilhouette.style.values.get('--tool-color')).toBe(selected.color)
    expect(heldRoot.dataset['cuttingHeld']).toBe('true')
  })

  it('renders synchronized visible colors and distinct silhouettes on both production tool surfaces', async () => {
    // Mutation caught: invisible/identical silhouettes or selector/model visible-color drift.
    server = await createServer({
      root: repositoryRoot,
      logLevel: 'silent',
      server: {
        host: '127.0.0.1',
        port: 0,
        watch: null,
      },
      plugins: [{
        name: 'tool-presentation-test-page',
        configureServer(vite) {
          vite.middlewares.use('/tool-presentation-test', (_request, response) => {
            response.statusCode = 200
            response.setHeader('content-type', 'text/html')
            response.end(`<!doctype html>
              <link rel="stylesheet" href="/game/style.css">
              <section id="selector" class="tool-selector"></section>
              <section id="held" class="held-tool-model">
                <span class="held-tool-silhouette tool-silhouette" data-held-tool-silhouette></span>
              </section>`)
          })
        },
      }],
    })
    await server.listen()
    const baseUrl = server.resolvedUrls?.local[0]
    if (baseUrl === undefined) throw new Error('Vite did not expose the production HUD')
    browser = await chromium.launch({ headless: true })
    const page = await browser.newPage({ viewport: { width: 1000, height: 700 } })
    await page.goto(`${baseUrl}tool-presentation-test`, { waitUntil: 'domcontentloaded' })
    await page.waitForFunction(() => [...document.styleSheets].some(({ href }) => href?.endsWith('/game/style.css')))

    const presentations = await page.evaluate(async (base) => {
      const load = (path: string): Promise<Record<string, any>> => (
        window.eval(`import(${JSON.stringify(`${base}${path}`)})`) as Promise<Record<string, any>>
      )
      const [
        { mountToolSelector, renderHeldToolModel },
        { ToolInventory, TOOL_CATALOG },
        { decodeToolContent, openingToolContent },
      ] = await Promise.all([
        load('game/tool-selector.ts'),
        load('src/game/tools.ts'),
        load('src/game/tools/content.ts'),
      ])
      const selectorRoot = document.querySelector<HTMLElement>('#selector')!
      const heldRoot = document.querySelector<HTMLElement>('#held')!
      const inventory = new ToolInventory(new Set(TOOL_CATALOG.map(({ id }: { id: string }) => id)), () => 100)
      inventory.cycle('1', 100)
      const content = decodeToolContent(openingToolContent.current.definitions.map((definition: {
        id: string
        name: string
        description: string
      }) => ({
        ...definition,
        name: `Visual ${definition.id}`,
        description: `Visual description for ${definition.id}.`,
      })))
      const selector = mountToolSelector(selectorRoot, () => content)
      selector.render(inventory, 101)
      const rows = [...selectorRoot.querySelectorAll<HTMLElement>('[data-tool-id]')]
      const held = heldRoot.querySelector<HTMLElement>('[data-held-tool-silhouette]')!
      const visibleColor = (element: HTMLElement, silhouette: string, surface: 'row' | 'held'): string => {
        const pseudo = getComputedStyle(element, silhouette === 'loop' && surface === 'held' ? '::after' : '::before')
        if (silhouette === 'sprout' && surface === 'row') return pseudo.backgroundColor
        if (silhouette === 'loop' && surface === 'held') return pseudo.borderLeftColor
        if (silhouette === 'sprout' && surface === 'held') return getComputedStyle(element, '::after').borderTopColor
        return pseudo.borderTopColor
      }
      const result = TOOL_CATALOG.map(({ id, color, silhouette }: { id: string; color: string; silhouette: string }) => {
        renderHeldToolModel(heldRoot, id, false)
        const row = rows.find((candidate) => candidate.dataset['toolId'] === id)!
        row.dataset['selected'] = 'false'
        const colorProbe = document.createElement('span')
        colorProbe.style.color = color
        document.body.append(colorProbe)
        const expectedColor = getComputedStyle(colorProbe).color
        colorProbe.remove()
        return {
          id,
          label: row.innerText,
          expectedLabel: content.definition(id).name,
          expectedColor,
          rowColor: visibleColor(row, silhouette, 'row'),
          heldColor: visibleColor(held, silhouette, 'held'),
        }
      })
      Object.assign(window, {
        __renderHeldToolForTest: (id: string) => renderHeldToolModel(heldRoot, id, false),
      })
      return result
    }, baseUrl)

    expect(presentations.map(({ label }: { label: string }) => label)).toEqual(
      presentations.map(({ expectedLabel }: { expectedLabel: string }) => expectedLabel),
    )
    for (const presentation of presentations) {
      expect(presentation.rowColor).toBe(presentation.expectedColor)
      expect(presentation.heldColor).toBe(presentation.expectedColor)
    }
    const rowImages: string[] = []
    const heldImages: string[] = []
    for (const { id } of TOOL_CATALOG) {
      rowImages.push((await page.locator(`[data-tool-id="${id}"]`).screenshot()).toString('base64'))
      await page.evaluate((toolId) => {
        ;(window as unknown as Window & { __renderHeldToolForTest(id: string): void }).__renderHeldToolForTest(toolId)
      }, id)
      heldImages.push((await page.locator('#held').screenshot()).toString('base64'))
    }
    expect(new Set(rowImages).size).toBe(TOOL_CATALOG.length)
    expect(new Set(heldImages).size).toBe(TOOL_CATALOG.length)

  }, 15_000)
})
