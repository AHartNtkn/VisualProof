import { orbited, panned, zoomed, type CamPose } from './camera'
import { lerp3, type Vec3 } from './vec3'

/** Glide time for click-to-focus retargeting. */
export const FOCUS_MS = 250

export type StationaryRelease = {
  readonly kind: 'stationary-release'
  readonly button: number
  readonly clientX: number
  readonly clientY: number
}

type PointerPosition = {
  readonly button: number
  readonly x: number
  readonly y: number
}

type FocusGlide = {
  readonly from: Vec3
  readonly to: Vec3
  readonly start: number
}

/** Owns the camera pose and the proof tree's orbit interaction state. */
export class OrbitInteraction {
  #pose: CamPose
  #drag: PointerPosition | null = null
  #press: PointerPosition | null = null
  #glide: FocusGlide | null = null

  constructor(initialPose: CamPose) {
    this.#pose = initialPose
  }

  get isGliding(): boolean {
    return this.#glide !== null
  }

  poseAt(now: number): CamPose {
    if (this.#glide === null) return this.#pose
    const t = Math.min(1, Math.max(0, (now - this.#glide.start) / FOCUS_MS))
    const eased = t * t * (3 - 2 * t)
    this.#pose = { ...this.#pose, target: lerp3(this.#glide.from, this.#glide.to, eased) }
    if (t >= 1) this.#glide = null
    return this.#pose
  }

  pointerDown(button: number, clientX: number, clientY: number): void {
    this.#drag = { button, x: clientX, y: clientY }
    this.#press = { button, x: clientX, y: clientY }
  }

  pointerMove(clientX: number, clientY: number, viewportHeight: number, now: number): boolean {
    if (this.#drag === null) return false
    const displayed = this.poseAt(now)
    const dx = clientX - this.#drag.x
    const dy = clientY - this.#drag.y
    this.#drag = { ...this.#drag, x: clientX, y: clientY }
    if (this.#drag.button === 2) {
      this.#glide = null
      this.#pose = panned(displayed, dx, dy, viewportHeight)
    } else {
      this.#pose = orbited(displayed, dx, dy)
    }
    return true
  }

  pointerUp(clientX: number, clientY: number): StationaryRelease | null {
    this.#drag = null
    const press = this.#press
    this.#press = null
    if (press === null || Math.hypot(clientX - press.x, clientY - press.y) >= 5) return null
    return {
      kind: 'stationary-release',
      button: press.button,
      clientX,
      clientY,
    }
  }

  cancelPointer(): void {
    this.#drag = null
    this.#press = null
  }

  wheel(deltaY: number, now: number): void {
    this.#pose = zoomed(this.poseAt(now), deltaY)
  }

  rotateYaw(delta: number, now: number): void {
    const displayed = this.poseAt(now)
    this.#pose = { ...displayed, yaw: displayed.yaw + delta }
  }

  changeHorizontalRadius(delta: number, minimum: number, now: number): void {
    const displayed = this.poseAt(now)
    const height = displayed.dist * Math.sin(displayed.pitch)
    const radius = Math.max(minimum, displayed.dist * Math.cos(displayed.pitch) + delta)
    this.#pose = {
      ...displayed,
      dist: Math.hypot(radius, height),
      pitch: Math.atan2(height, radius),
    }
  }

  changeHeight(delta: number, now: number): void {
    const displayed = this.poseAt(now)
    const radius = displayed.dist * Math.cos(displayed.pitch)
    const height = displayed.dist * Math.sin(displayed.pitch) + delta
    this.#pose = {
      ...displayed,
      dist: Math.hypot(radius, height),
      pitch: Math.atan2(height, radius),
    }
  }

  focus(target: Vec3, now: number): void {
    const displayed = this.poseAt(now)
    this.#glide = { from: displayed.target, to: target, start: now }
  }

  replacePose(pose: CamPose): void {
    this.#glide = null
    this.#pose = pose
  }
}
