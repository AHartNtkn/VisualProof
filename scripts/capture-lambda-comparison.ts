import { mkdir, mkdtemp, rm, writeFile } from 'node:fs/promises'
import { tmpdir } from 'node:os'
import { resolve } from 'node:path'
import { pathToFileURL } from 'node:url'
import { chromium, type Browser, type Page } from '@playwright/test'
import { build } from 'vite'

const ROOT = resolve(import.meta.dirname, '..')
const REFERENCE = '/home/ahart/Documents/gameProj/demos/lambda_tromp_reduction_demo_corrected.html'
const DEFAULT_OUTPUT = '/tmp/vpa-lambda-overviews'

const EXAMPLES = [
  { key: 'one-use', source: '(\\x. x) a', deletion: false },
  { key: 'duplication', source: '(\\f. \\x. f (f x)) (\\z. z)', deletion: false },
  { key: 'deletion', source: '(\\x. kept) ((\\z. z) discarded)', deletion: true },
  { key: 'nested-binder', source: '(\\x. \\y. x y) (\\w. w)', deletion: false },
  { key: 'capture-avoidance', source: '(\\x. \\y. x) y', deletion: false },
] as const

const STAGES = [
  { label: 'initial / identify', ordinary: 0.075, deletion: 0.075 },
  { label: 'duplicate / discard', ordinary: 0.245, deletion: 0.265 },
  { label: 'make space', ordinary: 0.44, deletion: 0.51 },
  { label: 'docking / contraction', ordinary: 0.68, deletion: 0.64 },
  { label: 'cleanup', ordinary: 0.9375, deletion: 0.785 },
  { label: 'final', ordinary: 1, deletion: 1 },
] as const

const MODES = [
  { key: 'reference', label: 'corrected reference' },
  { key: '2d-light', label: 'application 2D' },
  { key: '3d-light', label: 'application 3D · light' },
  { key: '3d-dark', label: 'application 3D · dark' },
] as const

type Mode = (typeof MODES)[number]['key']
type Capture = { readonly mode: Mode; readonly progress: number; readonly image: Buffer }

const HARNESS = String.raw`
import { DiagramBuilder } from '/src/kernel/diagram/builder.ts'
import { singleStepAction } from '/src/kernel/proof/action.ts'
import { parseTerm } from '/src/kernel/term/parse.ts'
import { stepNormalOrder } from '/src/kernel/term/reduce.ts'
import { MotionCoordinator, defaultMotionPreferences } from '/src/app/interact/motion.ts'
import { convertToWeakHeadNormal } from '/src/app/tactics.ts'
import { adaptCanvas } from '/src/view/canvas.ts'
import { fitCamera } from '/src/view/camera.ts'
import { carryOver, frameBounds, mkEngine } from '/src/view/engine.ts'
import { DARK, LIGHT, relationWireHues } from '/src/view/paint.ts'
import { seedProject, settle } from '/src/view/relax.ts'
import { fitPose } from '/src/view3d/camera.ts'
import { mountRender } from '/src/view3d/render.ts'
import { scene3 } from '/src/view3d/scene.ts'
import { planTransition, sceneAt } from '/src/view3d/transition.ts'

const canvas2 = document.querySelector('#two')
const host3 = document.querySelector('#three')
const surface2 = adaptCanvas(canvas2)
surface2.resize(900, 900)
let state = null
let currentTheme = LIGHT
let renderer3 = null

const renderTheme = (theme, diagram) => ({
  mode: theme.mode,
  background: theme.canvas,
  line: theme.mode === 'dark' ? '#f2f4f8' : theme.ink,
  lineAlt: theme.frame,
  baseWire: theme.wire,
  hover: theme.interaction.hover,
  hues: relationWireHues(diagram, theme.relationHueLightness),
})

function load(source) {
  const parsed = parseTerm(source)
  const reduced = stepNormalOrder(parsed.term)
  if (reduced === null) throw new Error('comparison source has no beta step')
  const builder = new DiagramBuilder()
  const node = builder.term(builder.root, parsed.term, parsed.freeIdentifiers.length)
  const sourceDiagram = builder.build()
  const conversion = convertToWeakHeadNormal(sourceDiagram, node, 1)
  const targetDiagram = conversion.diagram

  const sourceEngine = mkEngine(sourceDiagram, [])
  seedProject(sourceEngine)
  settle(sourceEngine, 4000)
  const targetEngine = mkEngine(targetDiagram, [])
  seedProject(targetEngine, false, carryOver(sourceEngine, targetEngine))
  settle(targetEngine, 4000)
  const frame = frameBounds(targetEngine)
  if (frame === null) throw new Error('comparison application did not establish a frame')

  currentTheme = LIGHT
  const motion = new MotionCoordinator({
    preferences: () => defaultMotionPreferences(false),
    engine: () => targetEngine,
    theme: () => currentTheme,
  })
  const lambdaTransition = motion.observeSwap(
    sourceEngine,
    targetEngine,
    0,
    singleStepAction('beta', conversion.step),
  )
  state = {
    sourceDiagram,
    targetDiagram,
    targetEngine,
    motion,
    view: fitCamera({ center: frame.center, radius: frame.frameR }, 900, 900, 1),
    sourceScene: scene3(sourceDiagram),
    targetScene: scene3(targetDiagram),
    lambdaTransition,
  }
  renderer3?.dispose()
  renderer3 = null
  host3.replaceChildren()
}

function show2d(progress) {
  host3.style.display = 'none'
  canvas2.style.display = 'block'
  currentTheme = LIGHT
  state.motion.scrubBeta(progress)
  surface2.render({
    background: currentTheme.canvas,
    layers: [{ shapes: state.motion.paint(0) }],
  }, state.view)
}

function show3d(progress, themeName) {
  canvas2.style.display = 'none'
  host3.style.display = 'block'
  currentTheme = themeName === 'dark' ? DARK : LIGHT
  const theme = renderTheme(currentTheme, state.targetDiagram)
  const transition = planTransition(
    state.sourceScene,
    state.targetScene,
    currentTheme.wire,
    state.lambdaTransition,
  )
  const presented = sceneAt(transition, progress)
  const center = transition.toBounds.center
  const radius = Math.max(transition.fromBounds.radius, transition.toBounds.radius) * 1.12
  const pose = fitPose(center, radius, 1)
  if (renderer3 === null) {
    renderer3 = mountRender(host3, theme)
    renderer3.resize(900, 900)
  } else {
    renderer3.setTheme(theme)
  }
  renderer3.setEntities(presented.entities)
  renderer3.setPose(pose)
  renderer3.render()
}

window.__lambdaComparison = { load, show2d, show3d }
`

function outputDirectory(): string {
  const position = process.argv.indexOf('--output')
  const value = position < 0 ? DEFAULT_OUTPUT : process.argv[position + 1]
  if (value === undefined) throw new Error('--output requires a directory')
  return resolve(value)
}

async function buildHarness(): Promise<{ readonly url: string; dispose(): Promise<void> }> {
  const built = await build({
    root: ROOT,
    logLevel: 'error',
    build: {
      write: false,
      target: 'esnext',
      rollupOptions: {
        input: 'virtual:lambda-comparison',
        output: { format: 'iife', name: 'LambdaComparison', inlineDynamicImports: true },
      },
    },
    plugins: [{
      name: 'lambda-comparison',
      resolveId(id) {
        return id === 'virtual:lambda-comparison' ? '\0lambda-comparison.ts' : null
      },
      load(id) {
        return id === '\0lambda-comparison.ts' ? HARNESS : null
      },
    }],
  })
  const outputs = (Array.isArray(built) ? built : [built]) as Array<{
    readonly output: readonly { readonly type: string; readonly code?: string }[]
  }>
  const code = outputs.flatMap(({ output }) => output)
    .find((item) => item.type === 'chunk')?.code
  if (code === undefined) throw new Error('Vite did not produce the comparison application')
  const directory = await mkdtemp(resolve(tmpdir(), 'vpa-lambda-capture-'))
  const html = resolve(directory, 'index.html')
  const script = code.replaceAll('</script', '<\\/script')
  await writeFile(html, `<!doctype html><style>html,body{margin:0;width:900px;height:900px;overflow:hidden}canvas{display:block}#two,#three{position:absolute;inset:0;width:900px;height:900px}</style><canvas id="two" width="900" height="900"></canvas><div id="three"></div><script>${script}</script>`)
  return {
    url: pathToFileURL(html).href,
    dispose: async () => rm(directory, { recursive: true, force: true }),
  }
}

async function loadReference(page: Page, source: string): Promise<void> {
  await page.evaluate((value) => {
    const input = document.querySelector('#input')
    const load = document.querySelector('#load')
    if (!(input instanceof HTMLTextAreaElement) || !(load instanceof HTMLButtonElement)) {
      throw new Error('corrected reference controls are unavailable')
    }
    input.value = value
    load.click()
  }, source)
}

async function captureReference(page: Page, progress: number): Promise<Buffer> {
  await page.evaluate((value) => {
    const demo = (window as unknown as {
      __lambdaDemo: { setPosition(value: number): void }
    }).__lambdaDemo
    demo.setPosition(value)
  }, progress)
  return page.locator('#canvas').screenshot({ type: 'png' })
}

async function loadApplication(page: Page, source: string): Promise<void> {
  await page.evaluate((value) => {
    const app = (window as unknown as {
      __lambdaComparison: { load(source: string): void }
    }).__lambdaComparison
    app.load(value)
  }, source)
}

async function captureApplication(page: Page, mode: Exclude<Mode, 'reference'>, progress: number): Promise<Buffer> {
  const selector = mode === '2d-light' ? '#two' : '#three canvas'
  await page.evaluate(({ selected, value }) => {
    const app = (window as unknown as {
      __lambdaComparison: {
        show2d(progress: number): void
        show3d(progress: number, theme: 'light' | 'dark'): void
      }
    }).__lambdaComparison
    if (selected === '2d-light') app.show2d(value)
    else app.show3d(value, selected === '3d-dark' ? 'dark' : 'light')
  }, { selected: mode, value: progress })
  return page.locator(selector).screenshot({ type: 'png' })
}

function escapeHtml(value: string): string {
  return value
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;')
}

async function writeOverview(
  page: Page,
  output: string,
  example: (typeof EXAMPLES)[number],
  captures: readonly Capture[],
): Promise<void> {
  const header = STAGES.map((stage) => `<b>${escapeHtml(stage.label)}</b>`).join('')
  const rows = MODES.map((mode) => {
    const cells = captures.filter((capture) => capture.mode === mode.key).map((capture) => (
      `<figure><img src="data:image/png;base64,${capture.image.toString('base64')}">`
      + `<figcaption>${capture.progress.toFixed(4)}</figcaption></figure>`
    )).join('')
    return `<section><h2>${escapeHtml(mode.label)}</h2>${cells}</section>`
  }).join('')
  await page.setViewportSize({ width: 1780, height: 1160 })
  await page.setContent(`<!doctype html><style>
    *{box-sizing:border-box}html,body{margin:0;background:#10161d;color:#edf3f7;font:13px system-ui}
    h1{height:56px;margin:0;padding:10px 18px;font-size:19px;line-height:24px}
    h1 small{display:block;color:#aebbc5;font:12px ui-monospace,monospace}
    .header,section{display:grid;grid-template-columns:150px repeat(6,270px);margin:0 5px}
    .header{height:36px}.header:before{content:''}.header b{display:flex;align-items:center;justify-content:center;border:1px solid #40505e}
    section{height:260px}h2{margin:0;display:flex;align-items:center;justify-content:center;text-align:center;border:1px solid #40505e;font-size:14px;padding:8px}
    figure{margin:0;padding:5px;border:1px solid #40505e;background:#18222c}
    img{display:block;width:258px;height:226px;object-fit:contain;background:#0b1015}
    figcaption{text-align:center;color:#b9c5cf;font:11px ui-monospace,monospace;margin-top:3px}
  </style><h1>${escapeHtml(example.key)}<small>${escapeHtml(example.source)}</small></h1><div class="header">${header}</div>${rows}`)
  await page.waitForFunction(() => [...document.images].every((image) => image.complete))
  await page.screenshot({ path: resolve(output, `${example.key}.png`), fullPage: true })
}

async function main(): Promise<void> {
  const output = outputDirectory()
  await mkdir(output, { recursive: true })
  let browser: Browser | null = null
  let harness: Awaited<ReturnType<typeof buildHarness>> | null = null
  try {
    harness = await buildHarness()
    browser = await chromium.launch({ headless: true })
    const context = await browser.newContext({ viewport: { width: 960, height: 960 }, deviceScaleFactor: 1 })
    await context.addInitScript('globalThis.__name = (target) => target')
    const referencePage = await context.newPage()
    await referencePage.goto(pathToFileURL(REFERENCE).href)
    await referencePage.waitForFunction(() => '__lambdaDemo' in window)
    const applicationPage = await context.newPage()
    await applicationPage.goto(harness.url)
    await applicationPage.waitForFunction(() => '__lambdaComparison' in window)
    const sheetPage = await context.newPage()

    for (const example of EXAMPLES) {
      await loadReference(referencePage, example.source)
      await loadApplication(applicationPage, example.source)
      const captures: Capture[] = []
      for (const mode of MODES) {
        for (const stage of STAGES) {
          const progress = example.deletion ? stage.deletion : stage.ordinary
          const image = mode.key === 'reference'
            ? await captureReference(referencePage, progress)
            : await captureApplication(applicationPage, mode.key, progress)
          captures.push({ mode: mode.key, progress, image })
        }
      }
      await writeOverview(sheetPage, output, example, captures)
      process.stdout.write(`${resolve(output, `${example.key}.png`)}\n`)
    }
  } finally {
    await browser?.close()
    await harness?.dispose()
  }
}

if (process.argv[1] !== undefined && import.meta.url === pathToFileURL(resolve(process.argv[1])).href) {
  main().catch((error: unknown) => {
    process.stderr.write(`${error instanceof Error ? error.stack ?? error.message : String(error)}\n`)
    process.exitCode = 1
  })
}
