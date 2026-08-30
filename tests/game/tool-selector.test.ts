import { readFileSync } from 'node:fs'
import { describe, expect, it } from 'vitest'
import { mountToolSelector, renderHeldToolModel } from '../../game/tool-selector'
import { ToolInventory } from '../../src/game/tools'
import { heldColorAuthorityViolations } from './held-color-authority'

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
  it('is empty when expired and otherwise shows the category and every acquired label once', () => {
    // Catches a permanent selected-tool HUD or acquired tools disappearing from the temporary reveal.
    const documentTarget = new TestDocument()
    const root = documentTarget.createElement()
    const inventory = new ToolInventory(new Set(['sprout-spawner', 'double-cut', 'iteration']), () => 100)
    const selector = mountToolSelector(root as unknown as HTMLElement)
    inventory.cycle('1', 100)

    selector.render(inventory, 101)
    const rows = descendants(root).filter(({ dataset }) => Object.hasOwn(dataset, 'toolId'))
    expect(root.children[0]?.textContent).toBe('1')
    expect(rows.map(({ textContent }) => textContent)).toEqual(['Sprout Spawner', 'Double Cut', 'Iteration'])
    expect(rows.filter(({ dataset }) => dataset['selected'] === 'true')).toHaveLength(1)
    expect(rows.find(({ dataset }) => dataset['selected'] === 'true')?.dataset['toolId']).toBe('double-cut')

    selector.render(inventory, 1900)
    expect(root.children).toHaveLength(0)
  })

  it('projects catalog silhouette and color metadata into selector rows and held models', () => {
    // Catches either visual surface inventing metadata outside TOOL_CATALOG.
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
    expect(rows.map(({ dataset, style }) => ({
      id: dataset['toolId'], silhouette: dataset['silhouette'], color: style.values.get('--tool-color'),
    }))).toEqual([
      { id: 'sprout-spawner', silhouette: 'sprout', color: '#8cbf26' },
      { id: 'double-cut', silhouette: 'nested-cuts', color: '#d76f3f' },
      { id: 'iteration', silhouette: 'loop', color: '#7166c9' },
    ])

    renderHeldToolModel(heldRoot as unknown as HTMLElement, 'iteration', true)
    expect(heldSilhouette.dataset).toMatchObject({ toolId: 'iteration', silhouette: 'loop' })
    expect(heldSilhouette.style.values.get('--tool-color')).toBe('#7166c9')
    expect(heldRoot.dataset['cuttingHeld']).toBe('true')
  })

  it('derives every held-model colored primitive from the catalog custom property', () => {
    // Catches a silhouette-specific background, border, shadow, or filter becoming a second color authority.
    const stylesheet = readFileSync(new URL('../../game/style.css', import.meta.url), 'utf8')
    expect(heldColorAuthorityViolations(stylesheet)).toEqual([])
  })

  it('rejects chromatic named, functional, and perceptual colors in every held color property', () => {
    // Catches a mixed declaration hiding a second hue authority beside currentcolor.
    const invalid = `
      .held-tool-silhouette { color: rebeccapurple; border-color: hsl(120 100% 50%); }
      .held-tool-silhouette::before {
        background: linear-gradient(currentcolor, #8cbf26, hwb(120 0% 0%), lab(50% 40 20), lch(50% 30 20));
        background-image: linear-gradient(currentcolor, rgb(140 191 38));
        outline-color: var(--rogue-color);
        fill: rebeccapurple;
        stroke: currentcolor;
        box-shadow: 0 0 2px oklab(.5 .1 .1), 0 0 4px oklch(.5 .2 120);
        filter: drop-shadow(0 0 2px color(display-p3 1 0 0)) hue-rotate(30deg);
      }
      @media (prefers-contrast: more) {
        .held-tool-silhouette::after { border-top-color: Highlight; }
      }
    `

    expect(heldColorAuthorityViolations(invalid).map(({ color }) => color)).toEqual([
      'rebeccapurple',
      'hsl(120 100% 50%)',
      '#8cbf26',
      'hwb(120 0% 0%)',
      'lab(50% 40 20)',
      'lch(50% 30 20)',
      'rgb(140 191 38)',
      'var(--rogue-color)',
      'rebeccapurple',
      'oklab(.5 .1 .1)',
      'oklch(.5 .2 120)',
      'color(display-p3 1 0 0)',
      'hue-rotate(30deg)',
      'Highlight',
    ])
  })

  it('allows currentcolor, transparency, and explicit equal-channel neutral shading', () => {
    // Catches the guard rejecting legitimate luminance and alpha treatment.
    const neutral = `
      .held-tool-silhouette {
        color: currentcolor;
        border-color: transparent;
        background: linear-gradient(currentcolor, #fff, rgb(12 12 12 / 40%), hsl(0 0% 20%));
        box-shadow: inset 0 0 #000, 0 0 hwb(20 50% 50%);
        filter: drop-shadow(0 0 2px oklch(.5 0 120));
      }
    `

    expect(heldColorAuthorityViolations(neutral)).toEqual([])
  })

  it('keeps ordinary HUD markup free of a permanent equipped-tool label', () => {
    // Catches temporary selection state being duplicated as permanent keyboard or equipment prose.
    const markup = readFileSync(new URL('../../game/index.html', import.meta.url), 'utf8')
    expect(markup).not.toMatch(/Equipped:|data-equipped-item-label|Press 1|No cutting held|Cutting held/)
  })
})
