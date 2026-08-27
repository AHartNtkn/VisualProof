mod commands;
mod mouse_capture;
pub mod save_store;

pub fn run() {
    let builder = tauri::Builder::default();
    #[cfg(feature = "wdio-tests")]
    let builder = builder
        .plugin(tauri_plugin_wdio::init())
        .plugin(tauri_plugin_wdio_webdriver::init());
    builder
        .invoke_handler(tauri::generate_handler![
            commands::list_slots,
            commands::create_slot,
            commands::load_slot,
            commands::update_tree,
            commands::update_camera,
            commands::set_game_mouse_capture
        ])
        .run(tauri::generate_context!())
        .expect("failed to run Orchard");
}

#[cfg(test)]
mod generated_save_tests {
    use super::save_store::{CameraRecord, SaveStore};
    use std::path::PathBuf;

    #[test]
    fn generated_saves_load_through_the_production_store() {
        let save_directory =
            PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../game/generated-saves");
        let store = SaveStore::new(save_directory);

        for count in [1, 10, 50, 100, 250, 500, 1000, 2000] {
            let slot_id = if count == 1 {
                "large-1".to_owned()
            } else {
                format!("stress-{count}")
            };
            let loaded = store.load(&slot_id).unwrap();

            assert_eq!(loaded.slot_id, slot_id);
            assert_eq!(
                loaded.display_name,
                if count == 1 {
                    "Large Tree".to_owned()
                } else {
                    format!("Renderer Stress {count}")
                }
            );
            assert_eq!(loaded.updated_at_ms, 0);
            assert_eq!(
                loaded.camera,
                if count == 1 {
                    CameraRecord {
                        x: 0.0,
                        y: 1.7,
                        z: 82.0,
                        yaw: -0.00841,
                        pitch: 0.15565,
                    }
                } else {
                    CameraRecord {
                        x: 0.0,
                        y: 1.7,
                        z: 82.0,
                        yaw: 0.0,
                        pitch: -0.04,
                    }
                }
            );
            assert_eq!(loaded.trees.len(), count);
            assert_eq!(loaded.diagrams.len(), 1);
        }
    }
}
