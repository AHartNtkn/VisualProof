import { invoke } from '@tauri-apps/api/core'
import type { TutorialContentDefinition } from './tutorial/content'
import type { ToolContentDefinition } from './tools/content'

export type AuthoredContentClient = {
  saveTutorial(records: readonly TutorialContentDefinition[]): Promise<void>
  saveTools(records: readonly ToolContentDefinition[]): Promise<void>
}

function decodeSavedAuthoredContent(value: unknown): void {
  if (value !== null) throw new Error('saved authored content response must be null')
}

export const authoredContentClient: AuthoredContentClient = {
  saveTutorial: (content) => invoke('save_tutorial_content', { input: { content } })
    .then(decodeSavedAuthoredContent),
  saveTools: (content) => invoke('save_tool_content', { input: { content } })
    .then(decodeSavedAuthoredContent),
}
