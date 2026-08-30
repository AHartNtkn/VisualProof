mod commands;
#[cfg(feature = "playtest-server")]
pub mod playtest_server;
pub mod save_store;

pub fn run() {
    let builder = tauri::Builder::default();
    #[cfg(feature = "wdio-tests")]
    let builder = builder
        .plugin(tauri_plugin_wdio::init())
        .plugin(tauri_plugin_wdio_webdriver::init());
    builder
        .invoke_handler(tauri::generate_handler![
            commands::quit_game,
            commands::list_slots,
            commands::create_slot,
            commands::load_slot,
            commands::insert_tree,
            commands::update_tree,
            commands::update_camera,
            commands::accept_order,
            commands::abandon_order,
            commands::complete_order,
            commands::set_tutorials_enabled,
            commands::complete_tutorial_milestone,
            commands::acquire_tool,
            commands::save_order_catalog
        ])
        .run(tauri::generate_context!())
        .expect("failed to run Orchard");
}

#[cfg(test)]
mod generated_save_tests {
    use super::save_store::{CameraRecord, OrderRecord, OrderStatus, SaveStore};
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
            assert_eq!(loaded.reputation, 0);
            assert!(loaded.tutorials_enabled);
            assert!(loaded.completed_tutorial_milestones.is_empty());
            assert_eq!(loaded.acquired_tool_ids, vec!["sprout-spawner"]);
            assert_eq!(
                loaded.orders,
                vec![
                    OrderRecord {
                        order_id: "blank-sprout".into(),
                        state: OrderStatus::Pending,
                        pot: None,
                    },
                    OrderRecord {
                        order_id: "irregular-double-cut-a".into(),
                        state: OrderStatus::Pending,
                        pot: None,
                    },
                    OrderRecord {
                        order_id: "irregular-double-cut-b".into(),
                        state: OrderStatus::Pending,
                        pot: None,
                    },
                    OrderRecord {
                        order_id: "single-double-cut".into(),
                        state: OrderStatus::Pending,
                        pot: None,
                    },
                ]
            );
        }
    }
}
