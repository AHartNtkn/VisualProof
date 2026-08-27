use crate::save_store::{
    CameraRecord, CreateSlotInput, LoadedSlot, SaveStore, SlotListEntry, TreeUpdate,
};
use tauri::Manager;

use crate::mouse_capture;

fn store(app: &tauri::AppHandle) -> Result<SaveStore, String> {
    let root = app
        .path()
        .app_data_dir()
        .map_err(|error| error.to_string())?;
    Ok(SaveStore::new(root.join("saves")))
}

#[tauri::command]
pub fn list_slots(app: tauri::AppHandle) -> Result<Vec<SlotListEntry>, String> {
    store(&app)?.list().map_err(|error| error.to_string())
}

#[tauri::command]
pub fn create_slot(app: tauri::AppHandle, input: CreateSlotInput) -> Result<SlotListEntry, String> {
    store(&app)?
        .create(input)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn load_slot(app: tauri::AppHandle, slot_id: String) -> Result<LoadedSlot, String> {
    store(&app)?
        .load(&slot_id)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn update_tree(
    app: tauri::AppHandle,
    slot_id: String,
    update: TreeUpdate,
) -> Result<i64, String> {
    store(&app)?
        .update_tree(&slot_id, update)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn update_camera(
    app: tauri::AppHandle,
    slot_id: String,
    camera: CameraRecord,
) -> Result<(), String> {
    store(&app)?
        .update_camera(&slot_id, camera)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn set_game_mouse_capture(window: tauri::WebviewWindow, captured: bool) -> Result<(), String> {
    mouse_capture::set_game_mouse_capture(&window, captured)
}
