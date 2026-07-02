/**
 * Ambient declarations for the parts of the File System Access API this app
 * uses that the pinned TypeScript lib.dom does not yet declare: the picker
 * entry points on Window and async iteration over a directory handle. The
 * handle/writable interfaces themselves are already in lib.dom; these merge
 * with them.
 */
interface Window {
  showDirectoryPicker(options?: { mode?: 'read' | 'readwrite' }): Promise<FileSystemDirectoryHandle>
  showSaveFilePicker(options?: {
    suggestedName?: string
    startIn?: FileSystemDirectoryHandle
    types?: readonly { description?: string; accept: Record<string, readonly string[]> }[]
  }): Promise<FileSystemFileHandle>
}

interface FileSystemDirectoryHandle {
  values(): AsyncIterableIterator<FileSystemHandle>
}
