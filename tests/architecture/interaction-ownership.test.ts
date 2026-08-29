import * as THREE from 'three'
import { readFileSync, readdirSync } from 'node:fs'
import { join } from 'node:path'
import { describe, expect, it } from 'vitest'
import {
  cameraPoseForSave,
  displayCameraPose,
  enterOrbit,
  exitOrbit,
  initialCameraState,
} from '../../src/game/camera'
import { snapshotFromDiagram } from '../../src/game/diagram-snapshot'
import type { GameTree } from '../../src/game/model'
import { DynamicTreeObjects } from '../../src/game/render/dynamic-tree'
import {
  applyPlacement,
  localPointToWorld,
  worldPointToLocal,
  worldSphere,
  type TreePlacement,
} from '../../src/game/render/placement'
import { makeTreeMaterialSource, type RenderTree } from '../../src/game/render/runtime'
import type { TreeRenderAsset } from '../../src/game/render/types'
import { gameSession, publishTreeMutation } from '../../src/game/session'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { entityColor } from '../../src/view3d/entity-style'
import { OrbitInteraction } from '../../src/view3d/orbit-interaction'
import type { RenderTheme } from '../../src/view3d/render'
import type { Entity, Scene3 } from '../../src/view3d/scene'
import { SCENE_TWEEN_MS, SceneTweenTrack } from '../../src/view3d/transition'

const shellSource = readFileSync('src/app/shell.ts', 'utf8')
const viewportSource = readFileSync('src/app/interact/viewport.ts', 'utf8')
const constructSource = readFileSync('src/app/interact/construct.ts', 'utf8')
const spawnSource = readFileSync('src/app/interact/spawn.ts', 'utf8')
const connectionSource = readFileSync('src/app/interact/connection.ts', 'utf8')
const movesSource = readFileSync('src/app/interact/moves.ts', 'utf8')
const appIndexSource = readFileSync('src/app/index.ts', 'utf8')

function productionTypeScriptFiles(directory: string): string[] {
  return readdirSync(directory, { withFileTypes: true })
    .flatMap((entry) => {
      const path = join(directory, entry.name)
      return entry.isDirectory()
        ? productionTypeScriptFiles(path)
        : entry.isFile() && entry.name.endsWith('.ts') ? [path] : []
    })
    .sort()
}

type ProductionSource = {
  readonly path: string
  readonly source: string
}

const productionAppSources: readonly ProductionSource[] =
  productionTypeScriptFiles('src/app').map((path) => ({
    path,
    source: readFileSync(path, 'utf8'),
  }))

function displacedRelationInputViolations(
  sources: readonly ProductionSource[],
): string[] {
  const violations: string[] = []
  const globallyDisplaced = [
    /relationJoinStep/,
    /relationSeverStep/,
    /wire-content-and-parameters/,
    /scope-and-occurrences/,
    /Join relation content/,
    /Sever relation/,
    /relationOccurrencePicker/,
    /relationOccurrenceCandidates/,
    /discoverRelationOccurrences/,
    /findRelationOccurrences/,
    /inferRelationOccurrences/,
    /PreparedMembrane/,
    /prepareMembraneContent/,
    /membraneCrossing/,
    /PendingMembrane/,
    /crossing tap/i,
  ] as const
  for (const { path, source } of sources) {
    for (const pattern of globallyDisplaced) {
      if (pattern.test(source)) violations.push(`${path}: ${pattern.source}`)
    }
    if (path !== 'src/app/interact/connection.ts') {
      for (const kind of ['relationJoin', 'relationSever']) {
        if (new RegExp(`kind:\\s*['"]${kind}['"]`).test(source)) {
          violations.push(`${path}: ${kind} gesture discriminator`)
        }
      }
      if (/kind:\s*['"]relation['"]/.test(source)) {
        violations.push(`${path}: relation durable-input discriminator`)
      }
    }
  }
  return violations
}

const canvasInteractionEvents = [
  'pointerdown', 'pointermove', 'pointerup', 'pointercancel',
  'lostpointercapture', 'pointerleave', 'contextmenu', 'dblclick', 'wheel',
] as const

function listenerPattern(event: string): RegExp {
  return new RegExp(`\\.addEventListener\\(\\s*['\"]${event}['\"]`)
}

describe('production interaction ownership', () => {
  it('keeps the shell free of the retired interaction controller', () => {
    for (const retiredName of [
      'interactionPrototype',
      'projectDragToSemanticFrontier',
      'commitBodyPositions',
    ]) {
      expect(shellSource, `src/app/shell.ts still contains ${retiredName}`).not.toContain(retiredName)
    }

    for (const event of canvasInteractionEvents) {
      expect(
        listenerPattern(event).test(shellSource),
        `src/app/shell.ts still installs a ${event} listener`,
      ).toBe(false)
    }
  })

  it('assigns production canvas interaction listeners to the viewport controller', () => {
    for (const event of canvasInteractionEvents) {
      expect(
        listenerPattern(event).test(viewportSource),
        `src/app/interact/viewport.ts must install a ${event} listener`,
      ).toBe(true)
    }
    for (const event of ['keydown', 'keyup']) {
      expect(listenerPattern(event).test(viewportSource), `viewport must own ${event}`).toBe(true)
    }
  })

  it('keeps construction policy and the spawn cascade free of global interaction lifecycles', () => {
    for (const [name, source] of [['construct', constructSource], ['spawn', spawnSource]] as const) {
      expect(source, `${name} must not listen on window`).not.toMatch(/window\.addEventListener/)
      expect(source, `${name} must not listen on document`).not.toMatch(/document\.addEventListener/)
      expect(source, `${name} must not listen on canvas`).not.toMatch(/canvas\.addEventListener/)
    }
  })

  it('does not retain the retired edit construction buttons', () => {
    for (const label of [
      'Add term', 'Add relation', 'Wrap in cut', 'Wrap in bubble',
      'Delete selection', 'Join two wires',
    ]) expect(shellSource).not.toContain(`button('${label}'`)
  })

  it('keeps severing on the slash gesture with no double-click mode', () => {
    for (const displaced of ['severMode', 'double-click strand', 'vpa-sever-option']) {
      expect(constructSource, `construction retains ${displaced}`).not.toContain(displaced)
      expect(shellSource, `shell retains ${displaced}`).not.toContain(displaced)
    }
  })

  it('has one shared proof controller and no backward/manual-picker interaction authority', () => {
    expect(shellSource.match(/new ProofMoveController/g)).toHaveLength(1)
    for (const displaced of [
      'type BackwardEntry',
      'backwardEntries',
      'commitBackward',
      "kind: 'unCite'",
      "kind: 'cite'",
      "kind: 'iterate'; readonly sel",
    ]) expect(shellSource, `shell retains displaced proof path ${displaced}`).not.toContain(displaced)
    expect(movesSource).not.toMatch(/window\.addEventListener|document\.addEventListener|canvas\.addEventListener/)
  })

  it('keeps relation quantifiers out of action menus and standalone constructors', () => {
    const actionsSource = readFileSync('src/app/actions.ts', 'utf8')
    for (const displaced of [
      "kind: 'relationJoin'",
      "kind: 'relationSever'",
      'wire-content-and-parameters',
      'scope-and-occurrences',
      'Join relation content',
      'Sever relation',
      'relationJoinStep',
      'relationSeverStep',
    ]) {
      expect(actionsSource + movesSource, `retains displaced relation input path ${displaced}`)
        .not.toContain(displaced)
    }
    expect(displacedRelationInputViolations(productionAppSources)).toEqual([])
    for (const kind of ['relationJoin', 'relationSever']) {
      expect(
        connectionSource.match(new RegExp(`kind:\\s*['"]${kind}['"]`, 'g')),
        `connection retains a displaced ${kind} gesture`,
      ).toBeNull()
      expect(
        movesSource.match(new RegExp(`case\\s+['"]${kind}['"]`, 'g')),
        `moves retains a displaced ${kind} branch`,
      ).toBeNull()
    }
    expect(
      connectionSource.match(/kind:\s*['"]relation['"]/g),
      'connection retains a displaced relation input type',
    ).toBeNull()
    expect(appIndexSource).not.toMatch(
      /ConnectionDragController|ProofMoveController|relationJoin|relationSever/,
    )
  })

  it('retires the ordered-selection occurrence designation machinery', () => {
    const brushSource = readFileSync('src/app/interact/brush.ts', 'utf8')
    expect(connectionSource).not.toContain('prepareSelectedOccurrences')
    expect(connectionSource).not.toContain('relationSelection')
    expect(connectionSource).not.toContain('PendingRelationState')
    expect(brushSource).toContain('[...selected, hit]')
    expect(displacedRelationInputViolations(productionAppSources)).toEqual([])
  })

  it('detects a competing relation input path anywhere in the production app surface', () => {
    expect(displacedRelationInputViolations([{
      path: 'src/app/interact/competing.ts',
      source: `
        export type Competing = { kind: 'relationJoin' }
        export function relationSeverStep() {
          return { rule: 'wireSever', input: { kind: 'relation' } }
        }
      `,
    }])).toEqual([
      'src/app/interact/competing.ts: relationSeverStep',
      'src/app/interact/competing.ts: relationJoin gesture discriminator',
      'src/app/interact/competing.ts: relation durable-input discriminator',
    ])
  })
})

const evenBranch: Extract<Entity, { kind: 'branch' }> = {
  kind: 'branch',
  key: 'drawing-even',
  region: 'region-even',
  polarity: 0,
  pts: [{ x: 0, y: 0, z: 0 }, { x: 0, y: 1, z: 0 }],
}

const oddBranch: Extract<Entity, { kind: 'branch' }> = {
  ...evenBranch,
  key: 'drawing-odd',
  region: 'region-odd',
  polarity: 1,
}

const strand: Extract<Entity, { kind: 'strand' }> = {
  kind: 'strand',
  key: 'drawing-strand',
  wire: 'wire-a',
  pts: [{ x: 0, y: 0, z: 0 }, { x: 1, y: 1, z: 0 }],
}

function scene(centerX: number, height: number): Scene3 {
  return {
    center: { x: centerX, y: height / 2, z: 0 },
    radius: Math.max(1, height),
    entities: [{
      ...evenBranch,
      pts: [{ x: centerX, y: 0, z: 0 }, { x: centerX, y: height, z: 0 }],
    }],
  }
}

function renderAsset(): TreeRenderAsset {
  const full = scene(0, 2)
  return {
    bounds: { center: full.center, radius: full.radius },
    lods: {
      full,
      reduced: full,
      marker: { color: '#ffffff', size: 1 },
    },
    hues: [['wire-a', '#12569a']],
    palette: { branch: '#2468ac', cutBranch: '#864220', baseWire: '#abcdef' },
    widths: { branch: 0.1, curve: 0.05 },
    glow: { color: '#ffffff', radius: 32, opacity: 0.65, bloom: 0.8 },
  }
}

describe('orchard cross-boundary interaction ownership', () => {
  it('makes orchard materials agree with the shared entity color authority', () => {
    const sharedTheme: RenderTheme = {
      mode: 'dark',
      background: '#000000',
      line: '#2468ac',
      lineAlt: '#864220',
      baseWire: '#abcdef',
      hover: '#ffffff',
      hues: new Map([['wire-a', '#12569a']]),
    }
    const asset = renderAsset()
    const authored = [evenBranch, oddBranch, strand].map((entity) =>
      entityColor(entity, sharedTheme.hues, sharedTheme))
    expect(authored).toEqual(['#2468ac', '#864220', '#12569a'])

    const materials = makeTreeMaterialSource(
      asset,
      new Set(),
      new Set(),
      new Set(),
      () => ({ width: 800, height: 600 }),
    )
    const orchard = [
      materials.line(evenBranch, asset.widths.branch),
      materials.line(oddBranch, asset.widths.branch),
      materials.line(strand, asset.widths.curve),
    ]
    const expectedRadiance = authored.map((color) =>
      new THREE.Color(color).multiplyScalar(1 + asset.glow.bloom).getHexString())

    expect(orchard.map((material) => material.color.getHexString())).toEqual(expectedRadiance)
    for (const material of orchard) material.dispose()
  })

  it('makes orchard dynamic transitions match the shared scene tween track', () => {
    const before = scene(0, 2)
    const after = scene(4, 6)
    const startedAt = 100
    const shared = new SceneTweenTrack(before, after, startedAt)
    const built: Scene3[] = []
    const suspended: string[] = []
    const resumed: RenderTree[] = []
    const tree: RenderTree = {
      id: 'tree-a',
      diagramJson: 'after',
      placement: { id: 'tree-a', index: 0, x: 0, z: 0, yaw: 0 },
    }
    const dynamic = new DynamicTreeObjects(
      new THREE.Group(),
      {
        suspend: (treeId) => { suspended.push(treeId) },
        resume: (target) => { resumed.push(target) },
      },
      (snapshot) => {
        built.push(snapshot)
        return new THREE.Group()
      },
      () => {},
    )

    const prepared = dynamic.prepare(tree, before, after, startedAt)
    dynamic.commit(prepared)
    expect(built.at(-1)).toEqual(shared.sample(startedAt))

    const halfway = startedAt + SCENE_TWEEN_MS / 2
    dynamic.update(halfway)
    expect(built.at(-1)).toEqual(shared.sample(halfway))
    expect(suspended).toEqual(['tree-a'])

    dynamic.update(startedAt + SCENE_TWEEN_MS)
    expect(resumed).toEqual([tree])
  })

  it('uses one placement transform for semantic points, bounds, and rendered objects', () => {
    const placement: TreePlacement = {
      id: 'tree-a', index: 0, x: 17, z: -11, yaw: Math.PI / 3,
    }
    const local = { x: 2, y: 4, z: -3 }
    const world = localPointToWorld(local, placement)
    const bounds = worldSphere({ center: local, radius: 5 }, placement)
    const object = new THREE.Object3D()
    applyPlacement(object, placement)
    object.updateMatrixWorld(true)
    const rendered = object.localToWorld(new THREE.Vector3(local.x, local.y, local.z))

    const roundTripped = worldPointToLocal(world, placement)
    expect(roundTripped.x).toBeCloseTo(local.x, 12)
    expect(roundTripped.y).toBeCloseTo(local.y, 12)
    expect(roundTripped.z).toBeCloseTo(local.z, 12)
    expect(bounds.center.x).toBeCloseTo(world.x, 12)
    expect(bounds.center.y).toBeCloseTo(world.y, 12)
    expect(bounds.center.z).toBeCloseTo(world.z, 12)
    expect(rendered.x).toBeCloseTo(world.x, 12)
    expect(rendered.y).toBeCloseTo(world.y, 12)
    expect(rendered.z).toBeCloseTo(world.z, 12)
  })

  it('leaves independently owned shared-orbit navigation unchanged during coherent publication', () => {
    const before: GameTree = {
      id: 'tree-a',
      snapshot: snapshotFromDiagram(new DiagramBuilder().build()),
      placement: { x: 0, z: -20, yaw: 0 },
    }
    const afterBuilder = new DiagramBuilder()
    afterBuilder.cut(afterBuilder.root)
    const after: GameTree = {
      ...before,
      snapshot: snapshotFromDiagram(afterBuilder.build()),
    }
    const mutation = { treeId: before.id, before, after }
    const session = gameSession(new Map([[before.id, before]]))
    const freePose = { position: { x: 3, y: 4, z: 8 }, yaw: 0.2, pitch: -0.1 }
    const navigation = enterOrbit(initialCameraState(freePose), {
      treeId: before.id,
      center: { x: 0, y: 2, z: -20 },
      radius: 4,
    })
    expect(navigation.interaction).toBeInstanceOf(OrbitInteraction)
    navigation.interaction.pointerDown(0, 10, 10)
    navigation.interaction.pointerMove(35, 18, 600, 0)
    const cameraBeforeProof = displayCameraPose(navigation, 0)

    let projected: GameTree = before
    let persisted: GameTree | null = null
    let discarded = 0
    const renderer = {
      prepareTreeUpdate: () => after,
      commitTreeUpdate: (prepared: GameTree) => { projected = prepared },
      discardTreeUpdate: () => { discarded += 1 },
    }

    expect(() => publishTreeMutation(session, mutation, renderer, () => {
      throw new Error('save queue unavailable')
    })).toThrow('save queue unavailable')
    expect(session.trees.get(before.id)).toBe(before)
    expect(projected).toBe(before)
    expect(discarded).toBe(1)
    expect(displayCameraPose(navigation, 0)).toEqual(cameraBeforeProof)

    publishTreeMutation(session, mutation, renderer, (tree) => { persisted = tree })
    expect(session.trees.get(before.id)).toBe(after)
    expect(projected).toBe(after)
    expect(persisted).toBe(after)
    expect(displayCameraPose(navigation, 0)).toEqual(cameraBeforeProof)
    expect(cameraPoseForSave(navigation)).toBe(freePose)
    expect(exitOrbit(navigation)).toEqual(initialCameraState(freePose))
  })
})
