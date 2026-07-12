import { readFileSync } from 'node:fs'
import { spawnSync } from 'node:child_process'
import { describe, expect, it } from 'vitest'

const install = 'scripts/assets/install-blender.sh'
const check = 'scripts/assets/check-blender.sh'

describe('interface asset Blender toolchain', () => {
  it('pins the exact LTS archive and refuses an unverified download', () => {
    const source = readFileSync(install, 'utf8')
    expect(source).toContain("VERSION='4.5.11'")
    expect(source).toContain("ARCHIVE='blender-4.5.11-linux-x64.tar.xz'")
    expect(source).toContain("SHA256='05ed7bd41bf3e61ae4f4a7cdc364c43088bf8b3fed702c2269c018fdf63a2188'")
    expect(source).toContain('sha256sum --check --status')
    expect(source).not.toContain('curl -k')
  })

  it('isolates concurrent extraction and validates the pinned release identity', () => {
    const installSource = readFileSync(install, 'utf8')
    const checkSource = readFileSync(check, 'utf8')
    expect(installSource).toContain('mktemp --directory "$ROOT/.tools/blender/.4.5.11-staging.XXXXXX"')
    expect(installSource).toContain(`trap 'rm -rf "$STAGING"' EXIT`)
    expect(installSource).not.toContain('STAGING="$ROOT/.tools/blender/.4.5.11-staging"')
    expect(installSource).toContain("grep -Fx 'Blender 4.5.11 LTS'")
    expect(checkSource).toContain("== 'Blender 4.5.11 LTS'")
  })

  it('serializes the complete version-scoped provisioning transaction', () => {
    const source = readFileSync(install, 'utf8')
    const lock = source.indexOf('LOCK="$ROOT/.tools/blender/$VERSION.provision.lock"')
    const acquire = source.indexOf('flock 9')
    const cacheObservation = source.indexOf('if [[ ! -f "$CACHE" ]]')
    const publication = source.indexOf(`printf '%s  %s\\n' "$SHA256" "$ARCHIVE" > "$DEST/ARCHIVE.sha256"`)
    expect(source).toContain('exec 9>"$LOCK"')
    expect(lock).toBeGreaterThan(-1)
    expect(acquire).toBeGreaterThan(lock)
    expect(cacheObservation).toBeGreaterThan(acquire)
    expect(publication).toBeGreaterThan(cacheObservation)
  })

  it('quotes the checked Blender executable path', () => {
    const source = readFileSync(check, 'utf8')
    expect(source).toContain('"$("$BIN" --version | head -n 1)"')
  })

  it.each([install, check])('%s has valid Bash syntax', (path) => {
    expect(spawnSync('bash', ['-n', path], { encoding: 'utf8' })).toMatchObject({ status: 0, stderr: '' })
  })
})
