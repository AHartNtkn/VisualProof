import { describe, expect, it } from 'vitest'
import { orbited, panned, zoomed, type CamPose } from '../../src/view3d/camera'
import { FOCUS_MS, OrbitInteraction } from '../../src/view3d/orbit-interaction'
import { lerp3, v3 } from '../../src/view3d/vec3'

const initial: CamPose = {
  target: v3(1, 2, 3),
  dist: 12,
  yaw: 0.4,
  pitch: 0.2,
}

describe('OrbitInteraction', () => {
  it('reports a stationary release with its button and release coordinates', () => {
    const orbit = new OrbitInteraction(initial)
    orbit.pointerDown(2, 100, 100)

    expect(orbit.pointerUp(102, 101)).toEqual({
      kind: 'stationary-release',
      button: 2,
      clientX: 102,
      clientY: 101,
    })
  })

  it('does not report a release displaced by the existing five-pixel threshold', () => {
    const orbit = new OrbitInteraction(initial)
    orbit.pointerDown(0, 100, 100)

    expect(orbit.pointerUp(103, 104)).toBeNull()
  })

  it('applies left orbit incrementally', () => {
    const orbit = new OrbitInteraction(initial)
    orbit.pointerDown(0, 10, 20)
    orbit.pointerMove(14, 18, 600, 0)
    orbit.pointerMove(20, 23, 600, 0)

    expect(orbit.poseAt(0)).toEqual(orbited(orbited(initial, 4, -2), 6, 5))
  })

  it('applies secondary pan incrementally', () => {
    const orbit = new OrbitInteraction(initial)
    orbit.pointerDown(2, 10, 20)
    orbit.pointerMove(14, 18, 600, 0)
    orbit.pointerMove(20, 23, 600, 0)

    expect(orbit.poseAt(0)).toEqual(panned(panned(initial, 4, -2, 600), 6, 5, 600))
  })

  it('applies wheel zoom to the currently displayed pose', () => {
    const orbit = new OrbitInteraction(initial)

    orbit.wheel(120, 0)

    expect(orbit.poseAt(0)).toEqual(zoomed(initial, 120))
  })

  it('glides focus to its target in 250 ms', () => {
    const orbit = new OrbitInteraction(initial)
    const target = v3(8, 9, 10)

    orbit.focus(target, 0)

    expect(orbit.poseAt(FOCUS_MS).target).toEqual(target)
  })

  it('samples the smoothstep focus path before completion', () => {
    const orbit = new OrbitInteraction(initial)
    const target = v3(9, 4, -2)
    orbit.focus(target, 0)

    expect(orbit.poseAt(FOCUS_MS / 4).target).toEqual(
      lerp3(initial.target, target, 0.25 * 0.25 * (3 - 2 * 0.25)),
    )
    expect(orbit.poseAt(FOCUS_MS / 2).target).toEqual(lerp3(initial.target, target, 0.5))
  })

  it('wheel zoom during a glide preserves and completes the focus movement', () => {
    const orbit = new OrbitInteraction(initial)
    const target = v3(9, 4, -2)
    orbit.focus(target, 0)
    const displayed = orbit.poseAt(FOCUS_MS / 2)

    orbit.wheel(120, FOCUS_MS / 2)

    const zoomedDisplayed = zoomed(displayed, 120)
    expect(orbit.poseAt(FOCUS_MS / 2)).toEqual(zoomedDisplayed)
    expect(orbit.poseAt(FOCUS_MS)).toEqual({ ...zoomedDisplayed, target })
  })

  it('left orbit during a glide preserves and completes the focus movement', () => {
    const orbit = new OrbitInteraction(initial)
    const target = v3(9, 4, -2)
    orbit.focus(target, 0)
    const displayed = orbit.poseAt(FOCUS_MS / 2)
    orbit.pointerDown(0, 10, 10)

    orbit.pointerMove(18, 4, 600, FOCUS_MS / 2)

    const orbitedDisplayed = orbited(displayed, 8, -6)
    expect(orbit.poseAt(FOCUS_MS / 2)).toEqual(orbitedDisplayed)
    expect(orbit.poseAt(FOCUS_MS)).toEqual({ ...orbitedDisplayed, target })
  })

  it('starts a pan from the currently displayed glide pose without a jump', () => {
    const orbit = new OrbitInteraction(initial)
    orbit.focus(v3(9, 4, -2), 0)
    const displayed = orbit.poseAt(FOCUS_MS / 2)
    orbit.pointerDown(2, 10, 10)

    orbit.pointerMove(14, 13, 600, FOCUS_MS / 2)

    expect(orbit.poseAt(FOCUS_MS / 2)).toEqual(panned(displayed, 4, 3, 600))
    expect(orbit.poseAt(FOCUS_MS).target).toEqual(panned(displayed, 4, 3, 600).target)
  })

  it('external pose replacement cancels a glide and becomes the sole pose', () => {
    const orbit = new OrbitInteraction(initial)
    orbit.focus(v3(9, 4, -2), 0)
    const replacement: CamPose = { target: v3(-5, 7, 2), dist: 3, yaw: -0.2, pitch: 0.7 }

    orbit.replacePose(replacement)

    expect(orbit.poseAt(FOCUS_MS)).toBe(replacement)
    expect(orbit.poseAt(FOCUS_MS * 2)).toBe(replacement)
  })
})
