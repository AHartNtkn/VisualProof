import { describe, expect, it } from 'vitest'
import { createQuitApplication } from '../../game/quit'

describe('quit application', () => {
  it('uses the native quit command in the desktop application', async () => {
    const commands: string[] = []
    const quit = createQuitApplication({
      native: true,
      invoke: async (command) => { commands.push(command) },
      close: () => {},
      closed: () => false,
    })

    await quit()

    expect(commands).toEqual(['quit_game'])
  })

  it('reports a browser refusal instead of pretending the game quit', async () => {
    let closes = 0
    const quit = createQuitApplication({
      native: false,
      invoke: async () => {},
      close: () => { closes += 1 },
      closed: () => false,
    })

    await expect(quit()).rejects.toThrow('Close this browser tab to quit the game.')
    expect(closes).toBe(1)
  })
})
