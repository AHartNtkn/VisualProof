const { contextBridge, ipcRenderer } = require('electron') as typeof import('electron')
const { createPlatformApi } = require('./preload-api.cjs') as typeof import('./preload-api.cjs')

contextBridge.exposeInMainWorld('cursebreakerPlatform', createPlatformApi(ipcRenderer))
