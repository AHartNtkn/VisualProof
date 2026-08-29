import { describe, expect, it } from 'vitest'
import {
  advanceCamera,
  cameraPoseForSave,
  displayCameraPose,
  enterOrbit,
  exitOrbit,
  initialCameraState,
} from '../../src/game/camera'
import { eyeOf, orbited } from '../../src/view3d/camera'

const start = { position: { x: 0, y: 1.7, z: 8 }, yaw: 0, pitch: 0 }
const target = {
  treeId: 'tree-a',
  center: { x: 0, y: 2, z: 0 },
  radius: 4,
}

describe('free-flight camera motion', () => {
  it('moves forward at the free-flight speed', () => {
    expect(advanceCamera(initialCameraState(start), {
      forward: 1, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    }, 1)).toMatchObject({
      mode: 'free', pose: { position: { x: 0, y: 1.7, z: 0 } },
    })
  })

  it('normalizes diagonal movement', () => {
    expect(advanceCamera(initialCameraState(start), {
      forward: 1, strafe: 1, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    }, 1)).toMatchObject({
      mode: 'free',
      pose: { position: { x: 8 / Math.sqrt(2), y: 1.7, z: 8 - 8 / Math.sqrt(2) } },
    })
  })

  it('cancels opposing axes', () => {
    expect(advanceCamera(initialCameraState(start), {
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 0,
    }, 1)).toMatchObject({ pose: { position: start.position } })
  })

  it('moves 24 units per second while sprinting', () => {
    expect(advanceCamera(initialCameraState(start), {
      forward: 1, strafe: 0, vertical: 0, sprint: true, lookX: 0, lookY: 0,
    }, 1)).toMatchObject({ pose: { position: { x: 0, y: 1.7, z: -16 } } })
  })

  it('applies horizontal mouse input to yaw', () => {
    expect(advanceCamera(initialCameraState(start), {
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 50, lookY: 0,
    }, 1)).toMatchObject({ pose: { yaw: -0.1 } })
  })

  it('lowers pitch from positive vertical mouse input', () => {
    expect(advanceCamera(initialCameraState(start), {
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 50,
    }, 1)).toMatchObject({ pose: { pitch: -0.1 } })
  })

  it('clamps pitch to the camera limits', () => {
    expect(advanceCamera(initialCameraState(start), {
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: -10000,
    }, 1)).toMatchObject({ pose: { pitch: Math.PI / 2 - 0.01 } })
    expect(advanceCamera(initialCameraState(start), {
      forward: 0, strafe: 0, vertical: 0, sprint: false, lookX: 0, lookY: 10000,
    }, 1)).toMatchObject({ pose: { pitch: -(Math.PI / 2 - 0.01) } })
  })

  it('applies mouse orientation without translating at zero seconds', () => {
    expect(advanceCamera(initialCameraState(start), {
      forward: 1, strafe: 1, vertical: 1, sprint: true, lookX: 50, lookY: 50,
    }, 0)).toMatchObject({
      pose: { position: start.position, yaw: -0.1, pitch: -0.1 },
    })
  })
})

describe('orbit camera motion and persistence', () => {
  it('keeps the exact free pose when orbit begins', () => {
    expect(enterOrbit(initialCameraState(start), target)).toMatchObject({
      mode: 'orbit', freePose: start,
    })
  })

  it('begins orbit at the free-flight eye', () => {
    const orbit = enterOrbit(initialCameraState(start), target)

    expect(displayCameraPose(orbit, 0).eye.x).toBeCloseTo(start.position.x, 12)
    expect(displayCameraPose(orbit, 0).eye.y).toBeCloseTo(start.position.y, 12)
    expect(displayCameraPose(orbit, 0).eye.z).toBeCloseTo(start.position.z, 12)
  })

  it('delegates orbit changes to the shared interaction', () => {
    const orbit = enterOrbit(initialCameraState(start), target)
    const initialPose = orbit.interaction.poseAt(0)
    orbit.interaction.pointerDown(0, 20, 30)
    orbit.interaction.pointerMove(44, 18, 600, 0)

    expect(orbit.interaction.poseAt(0)).toEqual(orbited(initialPose, 24, -12))
    expect(displayCameraPose(orbit, 0).eye).toEqual(eyeOf(orbited(initialPose, 24, -12)))
  })

  it('displays a normalized forward vector toward the target center', () => {
    const orbit = enterOrbit(initialCameraState(start), target)
    orbit.interaction.pointerDown(0, 0, 0)
    orbit.interaction.pointerMove(30, 20, 600, 0)
    const pose = displayCameraPose(orbit, 0)
    const orbitTarget = orbit.interaction.poseAt(0).target
    const towardCenter = {
      x: orbitTarget.x - pose.eye.x,
      y: orbitTarget.y - pose.eye.y,
      z: orbitTarget.z - pose.eye.z,
    }
    const directionLength = Math.hypot(towardCenter.x, towardCenter.y, towardCenter.z)

    expect(Math.hypot(pose.forward.x, pose.forward.y, pose.forward.z)).toBeCloseTo(1, 12)
    expect(
      pose.forward.x * towardCenter.x
      + pose.forward.y * towardCenter.y
      + pose.forward.z * towardCenter.z,
    ).toBeCloseTo(directionLength, 12)
  })

  it('restores the exact free state when orbit exits', () => {
    expect(exitOrbit(enterOrbit(initialCameraState(start), target)))
      .toEqual(initialCameraState(start))
  })

  it('saves the stored free pose while orbiting', () => {
    expect(cameraPoseForSave(enterOrbit(initialCameraState(start), target))).toEqual(start)
  })

  it('ignores free-flight keyboard motion while orbiting', () => {
    const orbit = enterOrbit(initialCameraState(start), target)
    expect(advanceCamera(orbit, {
      forward: 1, strafe: 1, vertical: 1, sprint: true, lookX: 50, lookY: 50,
    }, 1)).toBe(orbit)
  })
})
