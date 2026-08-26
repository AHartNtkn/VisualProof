import { describe, expect, it } from 'vitest'
import { DiagramBuilder } from '../../src/kernel/diagram/builder'
import { application, bound, free, lambda } from '../../src/kernel/term/term'
import { termGeometry } from '../../src/view/bend'
import { planBetaMotion, sampleBetaMotion } from '../../src/view/lambda-motion'
import { DARK, LIGHT } from '../../src/view/paint'
import {
  LAMBDA_SCALE,
  lambdaDiagram,
  lambdaPlane,
  type LambdaEntity,
} from '../../src/view3d/lambda'
import { layoutTree } from '../../src/view3d/layout'
import { presentedScene } from '../../src/view3d/index'
import { expandHover, focusPoint } from '../../src/view3d/pick'
import { entityColor, type RenderTheme } from '../../src/view3d/render'
import { scene3 } from '../../src/view3d/scene'
import { diagramSpec } from '../../src/view3d/spec'
import { planTransition, sceneAt } from '../../src/view3d/transition'
import { cross3, dist3, dot3, len3, norm3, segPointDist, sub3, v3 } from '../../src/view3d/vec3'

const term = application(lambda(application(bound(0), free(0))), free(1))

const renderTheme = (wire: string, mode: 'light' | 'dark'): RenderTheme => ({
  mode,
  background: '#000000',
  line: '#111111',
  lineAlt: '#222222',
  baseWire: wire,
  hover: '#ffffff',
  hues: new Map(),
})

describe('lambdaPlane', () => {
  it('returns an orthonormal basis normal to the incident branch', () => {
    // Would fail if the local figure were billboarded to the camera or embedded
    // in a fixed world plane instead of the term node's branch-normal plane.
    const tangent = v3(2, -3, 5)
    const plane = lambdaPlane(tangent)
    expect(len3(plane.right)).toBeCloseTo(1, 12)
    expect(len3(plane.up)).toBeCloseTo(1, 12)
    expect(len3(plane.normal)).toBeCloseTo(1, 12)
    expect(Math.abs(dot3(plane.right, plane.up))).toBeLessThan(1e-12)
    expect(Math.abs(dot3(plane.right, plane.normal))).toBeLessThan(1e-12)
    expect(Math.abs(dot3(plane.up, plane.normal))).toBeLessThan(1e-12)
    expect(Math.abs(dot3(plane.normal, norm3(tangent)))).toBeCloseTo(1, 12)
    expect(Math.abs(dot3(norm3(cross3(plane.right, plane.up)), plane.normal))).toBeCloseTo(1, 12)
  })
})

describe('lambdaDiagram', () => {
  it('embeds exactly the static termGeometry stroke graph as unfilled polylines in one branch-normal plane', () => {
    // Would fail if 3D invented a disk/mesh, dropped an exit stroke, or owned
    // a second static Lambda layout instead of decomposing termGeometry.
    const center = v3(4, -2, 7)
    const tangent = v3(1, 2, -1)
    const embedded = lambdaDiagram({ node: 'term', region: 'region', term, interfaceArity: 2, center, tangent })
    const geometry = termGeometry(term, 2)
    expect(embedded.strokes.map((stroke) => stroke.strokeId)).toEqual([
      ...geometry.arcs.map((_, index) => `arc:${index}`),
      ...geometry.radials.map((_, index) => `radial:${index}`),
      'exit:arc',
      'exit:line',
    ])
    expect(embedded.strokes.every((stroke) => stroke.kind === 'lambda')).toBe(true)
    expect(embedded.strokes.every((stroke) => !('fill' in stroke))).toBe(true)
    for (const stroke of embedded.strokes) {
      expect(stroke.node).toBe('term')
      expect(stroke.pts.length).toBeGreaterThanOrEqual(2)
      for (const point of stroke.pts) {
        expect(Math.abs(dot3(sub3(point, center), embedded.plane.normal))).toBeLessThan(1e-9)
      }
    }
  })

  it('maps output/free anchors by the same local-plane transform and carries subterm ownership', () => {
    // Would fail if wires still terminated on a generic ring or if picking
    // metadata collapsed every structural stroke to the whole term.
    const center = v3(-1, 3, 2)
    const tangent = v3(0, 0, 4)
    const embedded = lambdaDiagram({ node: 'term', region: 'region', term, interfaceArity: 2, center, tangent })
    const geometry = termGeometry(term, 2)
    for (const key of ['out', 'f:0', 'f:1']) {
      const local = geometry.portAnchors[key]!
      const actual = embedded.anchors.get(key)!
      const want = {
        x: center.x + LAMBDA_SCALE * (local.x * embedded.plane.right.x + local.y * embedded.plane.up.x),
        y: center.y + LAMBDA_SCALE * (local.x * embedded.plane.right.y + local.y * embedded.plane.up.y),
        z: center.z + LAMBDA_SCALE * (local.x * embedded.plane.right.z + local.y * embedded.plane.up.z),
      }
      expect(dist3(actual, want)).toBeLessThan(1e-12)
    }
    expect(embedded.strokes.some((stroke) => stroke.subtermPath.length > 0)).toBe(true)
  })

  it('uses the exact light/dark term-wire base colors until a motion frame supplies a structural color', () => {
    // Would fail if Lambda anatomy fell through to structural line/ink colors.
    const entity = lambdaDiagram({
      node: 'term', region: 'region', term, interfaceArity: 2, center: v3(0, 0, 0), tangent: v3(0, 1, 0),
    }).strokes[0]!
    expect(entity.color).toBeNull()
    expect(entityColor(entity, renderTheme(LIGHT.wire, 'light'))).toBe(LIGHT.wire)
    expect(entityColor(entity, renderTheme(DARK.wire, 'dark'))).toBe(DARK.wire)
    const moving: LambdaEntity = { ...entity, color: '#f06aa7' }
    expect(entityColor(moving, renderTheme(LIGHT.wire, 'light'))).toBe('#f06aa7')
    expect(entityColor(moving, renderTheme(DARK.wire, 'dark'))).toBe('#f06aa7')
  })

  it('embeds every coincident application-copy lambda bar as a nonzero circular polyline', () => {
    const source = application(
      lambda(lambda(application(bound(1), application(bound(1), bound(0))))),
      lambda(bound(0)),
    )
    const plan = planBetaMotion(source, { kind: 'beta', path: [] })

    for (const progress of [plan.times.spaceEnd, 1]) {
      const frame = sampleBetaMotion(plan, progress, '#26343a')
      const bars = lambdaDiagram({
        node: 'term', region: 'region', term: source, interfaceArity: 0,
        center: v3(0, 0, 0), tangent: v3(0, 1, 0), frame,
      }).strokes.filter(({ strokeId, role }) => strokeId.startsWith('copy:') && role === 'lambda')
      expect(bars).toHaveLength(2)
      for (const bar of bars) {
        expect(bar.pts.length).toBeGreaterThan(2)
        expect(bar.pts.slice(1).reduce((sum, point, index) => (
          sum + dist3(bar.pts[index]!, point)
        ), 0)).toBeGreaterThan(0.2)
      }
    }
  })
})

describe('3D scene integration', () => {
  it('places term strokes instead of a ring and uses their embedded anchors for IOTA strands', () => {
    // Would fail if scene/layout continued treating a term as a generic ring.
    const builder = new DiagramBuilder()
    const node = builder.term(builder.root, term, 2)
    const diagram = builder.build()
    const spec = diagramSpec(diagram)
    const layout = layoutTree(spec)
    const scene = scene3(diagram)
    const strokes = scene.entities.filter(
      (entity): entity is LambdaEntity => entity.kind === 'lambda' && entity.node === node,
    )
    expect(strokes.length).toBeGreaterThan(0)
    expect(scene.entities.some((entity) => entity.kind === 'ring' && entity.node === node)).toBe(false)
    expect(layout.lambdas.has(node)).toBe(true)
    const terminal = spec.wires.flatMap((wire) => wire.terminals).find((value) => value.node === node && value.portKey === 'out')!
    const strandEnds = scene.entities
      .filter((entity) => entity.kind === 'strand')
      .flatMap((entity) => [entity.pts[0]!, entity.pts[entity.pts.length - 1]!])
    expect(strandEnds.some((point) => dist3(point, layout.anchorOf(terminal)) < 1e-8)).toBe(true)
    for (const stroke of strokes) for (const point of stroke.pts) {
      expect(dist3(point, scene.center)).toBeLessThanOrEqual(scene.radius + 1e-9)
    }
  })

  it('samples Task 8 structural geometry and colors at the same transition progress', () => {
    // Would fail if 3D used generic whole-outline interpolation, eased the
    // structural timeline a second time, or recomputed lineage colors.
    const source = application(lambda(bound(0)), free(0))
    const target = free(0)
    const sourceBuilder = new DiagramBuilder()
    sourceBuilder.term(sourceBuilder.root, source, 1)
    const targetBuilder = new DiagramBuilder()
    targetBuilder.term(targetBuilder.root, target, 1)
    const previous = scene3(sourceBuilder.build())
    const next = scene3(targetBuilder.build())
    const baseColor = '#5bd2de'
    const progress = 0.1
    const frame = sampleBetaMotion(planBetaMotion(source, { kind: 'beta', path: [] }), progress, baseColor)
    const at = sceneAt(planTransition(previous, next, baseColor), progress)
    const strokes = at.entities.filter((entity): entity is LambdaEntity => entity.kind === 'lambda')
    const anatomy = strokes.filter((stroke) => !stroke.strokeId.startsWith('socket:'))
    expect(anatomy.map((stroke) => stroke.strokeId).sort()).toEqual(frame.strokes.map((stroke) => stroke.id).sort())
    expect(anatomy.map((stroke) => stroke.color).sort()).toEqual(frame.strokes.map((stroke) => stroke.color).sort())
    expect(strokes.some((stroke) => stroke.color === '#f06aa7')).toBe(true)
    const expectedSocket = frame.sockets.find((socket) => socket.amount > 0.002)!
    const socket = strokes.find((stroke) => stroke.strokeId === `socket:${expectedSocket.copyIndex}`)!
    expect('alpha' in socket ? socket.alpha : undefined).toBeCloseTo(expectedSocket.amount, 12)
    for (const stroke of strokes) for (const point of stroke.pts) {
      expect(Math.abs(dot3(sub3(point, stroke.center), stroke.plane.normal))).toBeLessThan(1e-9)
    }
    const transition = planTransition(previous, next, baseColor)
    const lambdaEntities = (entities: readonly { kind: string }[]) => entities.filter((entity) => entity.kind === 'lambda') as LambdaEntity[]
    const endpoints = [
      { progress: 0, staticEntities: lambdaEntities(previous.entities) },
      { progress: 1, staticEntities: lambdaEntities(next.entities) },
    ]
    for (const { progress, staticEntities } of endpoints) {
      const presented = lambdaEntities(sceneAt(transition, progress).entities)
      expect(presented.map(({ strokeId, pts }) => ({ strokeId, pts })))
        .toEqual(staticEntities.map(({ strokeId, pts }) => ({ strokeId, pts })))
    }
  })

  it('runs the same structural beta frame backward for reverse history', () => {
    // Would fail if undo fell back to index-paired static outline morphing.
    const source = application(lambda(bound(0)), free(0))
    const target = free(0)
    const sourceBuilder = new DiagramBuilder()
    sourceBuilder.term(sourceBuilder.root, source, 1)
    const targetBuilder = new DiagramBuilder()
    targetBuilder.term(targetBuilder.root, target, 1)
    const sourceScene = scene3(sourceBuilder.build())
    const targetScene = scene3(targetBuilder.build())
    const baseColor = '#26343a'
    const forwardProgress = 0.1
    const expected = sampleBetaMotion(
      planBetaMotion(source, { kind: 'beta', path: [] }),
      forwardProgress,
      baseColor,
    )
    const reverse = sceneAt(planTransition(targetScene, sourceScene, baseColor), 1 - forwardProgress)
    const anatomy = reverse.entities.filter(
      (entity): entity is LambdaEntity => entity.kind === 'lambda' && !entity.strokeId.startsWith('socket:'),
    )
    expect(anatomy.map((stroke) => stroke.strokeId).sort()).toEqual(expected.strokes.map((stroke) => stroke.id).sort())
    expect(anatomy.map((stroke) => stroke.color).sort()).toEqual(expected.strokes.map((stroke) => stroke.color).sort())
  })

  it('keeps a nested beta figure branch-normal and every explicit interface anchor attached during motion', () => {
    // Catches independent Lambda/branch pose interpolation, independent
    // strand endpoint interpolation, root-only beta detection, and loss of a
    // genuinely unused explicit free slot from the sampled frame.
    const source = lambda(application(lambda(bound(0)), free(0)))
    const target = lambda(free(0))
    const build = (value: typeof source) => {
      const builder = new DiagramBuilder()
      const termRegion = builder.cut(builder.root)
      const sibling = builder.cut(builder.root)
      const node = builder.term(termRegion, value, 2)
      builder.point(sibling)
      return { diagram: builder.build(), node, termRegion }
    }
    const before = build(source)
    const after = build(target)
    const progress = 0.1
    const transient = sceneAt(planTransition(
      scene3(before.diagram),
      scene3(after.diagram),
      '#5bd2de',
    ), progress)
    const branch = transient.entities.find(
      (entity): entity is Extract<(typeof transient.entities)[number], { kind: 'branch' }> => (
        entity.kind === 'branch' && entity.key === `b:${before.termRegion}`
      ),
    )!
    const strokes = transient.entities.filter(
      (entity): entity is LambdaEntity => entity.kind === 'lambda' && entity.node === before.node,
    )
    expect(strokes.length).toBeGreaterThan(0)
    const center = strokes[0]!.center
    const tangent = norm3(sub3(branch.pts[branch.pts.length - 1]!, branch.pts[0]!))
    expect(segPointDist(center, branch.pts[0]!, branch.pts[branch.pts.length - 1]!)).toBeLessThan(1e-10)
    expect(1 - Math.abs(dot3(tangent, strokes[0]!.plane.normal))).toBeLessThan(1e-10)
    for (const stroke of strokes) for (const point of stroke.pts) {
      expect(Math.abs(dot3(sub3(point, center), tangent))).toBeLessThan(1e-10)
    }

    expect(strokes.some((stroke) => stroke.strokeId === 'root/body/fn:lambda')).toBe(true)
    expect(strokes.some((stroke) => stroke.strokeId === 'interface:free:1:rail')).toBe(true)
    const anchors = [
      strokes.find((stroke) => stroke.strokeId === 'interface:output:line')!.pts.at(-1)!,
      strokes.find((stroke) => stroke.strokeId === 'interface:free:0:port-stem')!.pts.at(-1)!,
      strokes.find((stroke) => stroke.strokeId === 'interface:free:1:port-stem')!.pts.at(-1)!,
    ]
    const strandEnds = transient.entities
      .filter((entity) => entity.kind === 'strand')
      .flatMap((entity) => [entity.pts[0]!, entity.pts[entity.pts.length - 1]!])
    for (const anchor of anchors) {
      expect(Math.min(...strandEnds.map((point) => dist3(point, anchor)))).toBeLessThan(1e-10)
    }
  })

  it('picks root-owned Lambda anatomy as the whole term, including incident strands and focus bounds', () => {
    // Would fail if Lambda keys were opaque to the picking layer or focus
    // considered only one small source stroke instead of its owned subterm.
    const builder = new DiagramBuilder()
    const node = builder.term(builder.root, term, 2)
    const diagram = builder.build()
    const spec = diagramSpec(diagram)
    const scene = scene3(diagram)
    const strokes = scene.entities.filter(
      (entity): entity is LambdaEntity => entity.kind === 'lambda' && entity.node === node,
    )
    const rootStroke = strokes.find((stroke) => stroke.subtermPath.length === 0)!
    const expanded = expandHover(rootStroke.key, spec, scene.entities)
    for (const stroke of strokes) expect(expanded.has(stroke.key)).toBe(true)
    const incidentWires = new Set(spec.wires.filter((wire) => wire.terminals.some((terminal) => terminal.node === node)).map((wire) => wire.id))
    const incidentStrands = scene.entities.filter((entity) => entity.kind === 'strand' && incidentWires.has(entity.wire))
    expect(incidentStrands.length).toBeGreaterThan(0)
    for (const strand of incidentStrands) expect(expanded.has(strand.key)).toBe(true)

    let lo = v3(Infinity, Infinity, Infinity), hi = v3(-Infinity, -Infinity, -Infinity)
    for (const stroke of strokes) for (const point of stroke.pts) {
      lo = v3(Math.min(lo.x, point.x), Math.min(lo.y, point.y), Math.min(lo.z, point.z))
      hi = v3(Math.max(hi.x, point.x), Math.max(hi.y, point.y), Math.max(hi.z, point.z))
    }
    expect(dist3(focusPoint(rootStroke.key, scene.entities)!, v3(
      (lo.x + hi.x) / 2,
      (lo.y + hi.y) / 2,
      (lo.z + hi.z) / 2,
    ))).toBeLessThan(1e-9)
  })

  it('uses the presented transient scene for nested-subterm hover and focus', () => {
    const source = lambda(application(lambda(bound(0)), free(0)))
    const target = lambda(free(0))
    const build = (value: typeof source) => {
      const builder = new DiagramBuilder()
      const node = builder.term(builder.root, value, 1)
      return { diagram: builder.build(), node }
    }
    const before = build(source)
    const after = build(target)
    const targetScene = scene3(after.diagram)
    const shown = presentedScene(
      targetScene,
      planTransition(scene3(before.diagram), targetScene, '#5bd2de'),
      0.1,
    )
    const hit = shown.entities.find((entity): entity is LambdaEntity => (
      entity.kind === 'lambda'
      && entity.node === before.node
      && entity.strokeId === 'root/body/fn:lambda'
    ))!
    expect(targetScene.entities.some((entity) => entity.key === hit.key)).toBe(false)
    const expanded = expandHover(hit.key, diagramSpec(after.diagram), shown.entities)
    expect(expanded.has(hit.key)).toBe(true)
    const owned = shown.entities.filter((entity): entity is LambdaEntity => (
      entity.kind === 'lambda'
      && entity.node === hit.node
      && hit.subtermPath.every((segment, index) => entity.subtermPath[index] === segment)
    ))
    expect(owned.length).toBeGreaterThan(1)
    for (const entity of owned) expect(expanded.has(entity.key)).toBe(true)
    expect(focusPoint(hit.key, targetScene.entities)).toBeNull()
    let lo = v3(Infinity, Infinity, Infinity), hi = v3(-Infinity, -Infinity, -Infinity)
    for (const entity of owned) for (const point of entity.pts) {
      lo = v3(Math.min(lo.x, point.x), Math.min(lo.y, point.y), Math.min(lo.z, point.z))
      hi = v3(Math.max(hi.x, point.x), Math.max(hi.y, point.y), Math.max(hi.z, point.z))
    }
    expect(dist3(focusPoint(hit.key, shown.entities)!, v3(
      (lo.x + hi.x) / 2,
      (lo.y + hi.y) / 2,
      (lo.z + hi.z) / 2,
    ))).toBeLessThan(1e-10)
  })
})
