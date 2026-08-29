use crate::save_store::{
    CameraRecord, CreateSlotInput, LoadedSlot, PotPlacementRecord, SaveStore, SlotListEntry,
    TreeUpdate,
};
use tauri::Manager;

#[tauri::command]
pub fn quit_game(app: tauri::AppHandle) {
    app.exit(0);
}

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
pub fn insert_tree(
    app: tauri::AppHandle,
    slot_id: String,
    update: TreeUpdate,
) -> Result<i64, String> {
    store(&app)?
        .insert_tree(&slot_id, update)
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
pub fn accept_order(
    app: tauri::AppHandle,
    slot_id: String,
    order_id: String,
    pot: PotPlacementRecord,
) -> Result<(), String> {
    store(&app)?
        .accept_order(&slot_id, &order_id, pot)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn abandon_order(
    app: tauri::AppHandle,
    slot_id: String,
    order_id: String,
) -> Result<(), String> {
    store(&app)?
        .abandon_order(&slot_id, &order_id)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn complete_order(
    app: tauri::AppHandle,
    slot_id: String,
    order_id: String,
    reward: i64,
) -> Result<i64, String> {
    store(&app)?
        .complete_order(&slot_id, &order_id, reward)
        .map_err(|error| error.to_string())
}
