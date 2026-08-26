mod commands;
pub mod save_store;

pub fn run() {
    tauri::Builder::default()
        .invoke_handler(tauri::generate_handler![
            commands::list_slots,
            commands::create_slot,
            commands::load_slot,
            commands::update_tree,
            commands::update_camera
        ])
        .run(tauri::generate_context!())
        .expect("failed to run Orchard");
}
