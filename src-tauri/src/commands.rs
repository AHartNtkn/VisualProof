use crate::save_store::{
    AuthoredContentStore, CameraRecord, CreateSlotInput, LoadedSlot, OrderContentRecord,
    OrderContentStore, PotPlacementRecord, SaveStore, SlotListEntry, ToolContentRecord, TreeUpdate,
    TutorialContentRecord,
};
use serde::Deserialize;
use tauri::Manager;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TutorialContentInput {
    content: Vec<TutorialContentRecord>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ToolContentInput {
    content: Vec<ToolContentRecord>,
}

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

#[tauri::command]
pub fn set_tutorials_enabled(
    app: tauri::AppHandle,
    slot_id: String,
    enabled: bool,
) -> Result<(), String> {
    store(&app)?
        .set_tutorials_enabled(&slot_id, enabled)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn complete_tutorial_milestone(
    app: tauri::AppHandle,
    slot_id: String,
    milestone_id: String,
) -> Result<(), String> {
    store(&app)?
        .complete_tutorial_milestone(&slot_id, &milestone_id)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn acquire_tool(app: tauri::AppHandle, slot_id: String, tool_id: String) -> Result<(), String> {
    store(&app)?
        .acquire_tool(&slot_id, &tool_id)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn save_order_catalog(
    app: tauri::AppHandle,
    slot_id: String,
    content: Vec<OrderContentRecord>,
) -> Result<(), String> {
    OrderContentStore::production()
        .save_order_catalog(&store(&app)?, &slot_id, content)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn save_tutorial_content(input: TutorialContentInput) -> Result<(), String> {
    AuthoredContentStore::production()
        .save_tutorial_content(input.content)
        .map_err(|error| error.to_string())
}

#[tauri::command]
pub fn save_tool_content(input: ToolContentInput) -> Result<(), String> {
    AuthoredContentStore::production()
        .save_tool_content(input.content)
        .map_err(|error| error.to_string())
}
