const DEVELOPER_TOOLS_KEY = 'orchard.developerTools'

export type PreferenceStorage = Pick<Storage, 'getItem' | 'setItem'>

export class DeveloperPreferences {
  public constructor(private readonly storage: PreferenceStorage = localStorage) {}

  public get developerToolsEnabled(): boolean {
    return this.storage.getItem(DEVELOPER_TOOLS_KEY) === 'true'
  }

  public setDeveloperToolsEnabled(enabled: boolean): void {
    this.storage.setItem(DEVELOPER_TOOLS_KEY, String(enabled))
  }
}
