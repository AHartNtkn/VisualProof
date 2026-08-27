use orchard_game::save_store::{CameraRecord, CreateSlotInput, SaveStore, TreeUpdate};
use serde::Deserialize;
use std::error::Error;
use std::io;
use std::path::{Path, PathBuf};

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct EmitterInput {
    output_directory: PathBuf,
    saves: Vec<EmitterSave>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct EmitterSave {
    slot_id: String,
    filename: String,
    display_name: String,
    updated_at_ms: i64,
    camera: CameraRecord,
    trees: Vec<EmitterTree>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct EmitterTree {
    id: String,
    #[serde(rename = "index")]
    _index: usize,
    x: f64,
    z: f64,
    yaw: f64,
    diagram_json: String,
}

fn invalid_input(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message.into())
}

fn main() -> Result<(), Box<dyn Error>> {
    let input: EmitterInput = serde_json::from_reader(io::stdin().lock())?;
    let store = SaveStore::new(input.output_directory.clone());

    for save in input.saves {
        let expected_filename = format!("{}.sqlite3", save.slot_id);
        if save.filename != expected_filename || Path::new(&save.filename).components().count() != 1
        {
            return Err(invalid_input(format!(
                "filename '{}' must be exactly '{expected_filename}'",
                save.filename
            ))
            .into());
        }
        let destination = input.output_directory.join(&save.filename);
        let trees = save
            .trees
            .into_iter()
            .map(|tree| TreeUpdate {
                tree_id: tree.id,
                diagram_json: tree.diagram_json,
                x: tree.x,
                z: tree.z,
                yaw: tree.yaw,
            })
            .collect();
        store.create_at(
            &destination,
            &save.slot_id,
            save.updated_at_ms,
            CreateSlotInput {
                display_name: save.display_name,
                camera: save.camera,
                trees,
            },
        )?;
        store.load(&save.slot_id)?;
    }

    Ok(())
}
