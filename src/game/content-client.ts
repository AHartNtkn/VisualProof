import { invoke } from '@tauri-apps/api/core'
import type { TutorialContentDefinition } from './tutorial/content'
import type { ToolContentDefinition } from './tools/content'

export type AuthoredContentClient = {
  saveTutorial(records: readonly TutorialContentDefinition[]): Promise<void>
  saveTools(records: readonly ToolContentDefinition[]): Promise<void>
}

export type AuthoredContentOperation = 'save-tutorial' | 'save-tools'

export type AuthoredContentTransport = {
  request(operation: AuthoredContentOperation, input: Record<string, unknown>): Promise<unknown>
}

function decodeSavedAuthoredContent(value: unknown): void {
  if (value !== null) throw new Error('saved authored content response must be null')
}

export function createAuthoredContentClient(
  transport: AuthoredContentTransport,
): AuthoredContentClient {
  return {
    saveTutorial: (content) => transport.request('save-tutorial', { content })
      .then(decodeSavedAuthoredContent),
    saveTools: (content) => transport.request('save-tools', { content })
      .then(decodeSavedAuthoredContent),
  }
}

export const tauriAuthoredContentTransport: AuthoredContentTransport = {
  request(operation, input) {
    return invoke(operation === 'save-tutorial'
      ? 'save_tutorial_content'
      : 'save_tool_content', input)
  },
}

export function httpAuthoredContentTransport(config: {
  baseUrl: string
  token: string
  fetch: typeof globalThis.fetch
}): AuthoredContentTransport {
  const baseUrl = config.baseUrl.replace(/\/$/, '')
  return {
    async request(operation, input): Promise<unknown> {
      const document = operation === 'save-tutorial' ? 'tutorial' : 'tools'
      let response: Response
      try {
        response = await config.fetch.call(
          globalThis,
          `${baseUrl}/__orchard_playtest/content/${document}`,
          {
            method: 'POST',
            headers: {
              'content-type': 'application/json',
              'x-orchard-playtest-token': config.token,
            },
            body: JSON.stringify(input),
          },
        )
      } catch (error) {
        const detail = error instanceof Error ? error.message : String(error)
        throw new Error(`browser playtest content service unavailable: ${detail}`)
      }
      if (!response.ok) throw new Error(await response.text())
      return response.json()
    },
  }
}

export function selectAuthoredContentTransport(config: {
  transportName: string
  baseUrl?: string
  token?: string
  fetch: typeof globalThis.fetch
}): AuthoredContentTransport {
  switch (config.transportName) {
    case 'tauri': return tauriAuthoredContentTransport
    case 'playtest-http': {
      const { baseUrl, token } = config
      if (baseUrl === undefined || baseUrl.trim().length === 0
        || token === undefined || token.trim().length === 0) {
        throw new Error(
          'playtest HTTP content transport requires VITE_ORCHARD_PLAYTEST_URL and VITE_ORCHARD_PLAYTEST_TOKEN',
        )
      }
      return httpAuthoredContentTransport({ baseUrl, token, fetch: config.fetch })
    }
    default: throw new Error(`unsupported Orchard content transport '${config.transportName}'`)
  }
}

export const authoredContentClient = createAuthoredContentClient(selectAuthoredContentTransport({
  transportName: import.meta.env.VITE_ORCHARD_SAVE_TRANSPORT ?? 'tauri',
  baseUrl: import.meta.env.VITE_ORCHARD_PLAYTEST_URL,
  token: import.meta.env.VITE_ORCHARD_PLAYTEST_TOKEN,
  fetch: globalThis.fetch,
}))
