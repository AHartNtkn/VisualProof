use rusqlite::{params, Connection, OpenFlags, OptionalExtension, Transaction};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};
use thiserror::Error;
use uuid::Uuid;

const SCHEMA: &str = "
CREATE TABLE metadata (
  singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
  slot_id TEXT NOT NULL UNIQUE,
  display_name TEXT NOT NULL,
  updated_at_ms INTEGER NOT NULL
);
CREATE TABLE camera (
  singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
  x REAL NOT NULL, y REAL NOT NULL, z REAL NOT NULL,
  yaw REAL NOT NULL, pitch REAL NOT NULL
);
CREATE TABLE diagrams (
  diagram_key INTEGER PRIMARY KEY,
  diagram_json TEXT NOT NULL UNIQUE
);
CREATE TABLE trees (
  tree_id TEXT PRIMARY KEY,
  diagram_key INTEGER NOT NULL REFERENCES diagrams(diagram_key),
  x REAL NOT NULL, z REAL NOT NULL, yaw REAL NOT NULL
);
";

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CameraRecord {
    pub x: f64,
    pub y: f64,
    pub z: f64,
    pub yaw: f64,
    pub pitch: f64,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TreeUpdate {
    pub tree_id: String,
    pub diagram_json: String,
    pub x: f64,
    pub z: f64,
    pub yaw: f64,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CreateSlotInput {
    pub display_name: String,
    pub camera: CameraRecord,
    pub trees: Vec<TreeUpdate>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct TreeRecord {
    pub tree_id: String,
    pub diagram_key: i64,
    pub x: f64,
    pub z: f64,
    pub yaw: f64,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagramRecord {
    pub diagram_key: i64,
    pub diagram_json: String,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct LoadedSlot {
    pub slot_id: String,
    pub display_name: String,
    pub updated_at_ms: i64,
    pub camera: CameraRecord,
    pub trees: Vec<TreeRecord>,
    pub diagrams: Vec<DiagramRecord>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct SlotListEntry {
    pub slot_id: String,
    pub display_name: String,
    pub updated_at_ms: i64,
    pub error: Option<String>,
}

#[derive(Debug, Error)]
pub enum SaveStoreError {
    #[error("invalid slot id")]
    InvalidSlotId,
    #[error("save slot '{0}' was not found")]
    SlotNotFound(String),
    #[error("tree '{0}' was not found")]
    TreeNotFound(String),
    #[error("camera coordinates must be finite")]
    NonFiniteCamera,
    #[error("tree coordinates must be finite")]
    NonFiniteTree,
    #[error("save database has an invalid structure")]
    InvalidStructure,
    #[error("slot id must match the destination file stem")]
    DestinationStemMismatch,
    #[error("save destination must have a .sqlite3 extension")]
    InvalidDestinationExtension,
    #[error("save destination already exists")]
    DestinationExists,
    #[error("system clock is before the Unix epoch")]
    InvalidSystemClock,
    #[error("save timestamp cannot be advanced")]
    TimestampOverflow,
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Sqlite(#[from] rusqlite::Error),
}

pub type Result<T> = std::result::Result<T, SaveStoreError>;

#[derive(Clone, Debug)]
pub struct SaveStore {
    slot_directory: PathBuf,
}

impl SaveStore {
    pub fn new(slot_directory: PathBuf) -> Self {
        Self { slot_directory }
    }

    pub fn list(&self) -> Result<Vec<SlotListEntry>> {
        if !self.slot_directory.exists() {
            return Ok(Vec::new());
        }

        let mut paths = Vec::new();
        for entry in fs::read_dir(&self.slot_directory)? {
            let entry = entry?;
            if entry.file_type()?.is_file()
                && entry.path().extension().and_then(|value| value.to_str()) == Some("sqlite3")
            {
                paths.push(entry.path());
            }
        }
        paths.sort();

        Ok(paths
            .into_iter()
            .map(|path| {
                let slot_id = path
                    .file_stem()
                    .and_then(|value| value.to_str())
                    .unwrap_or_default()
                    .to_owned();
                match self.load(&slot_id) {
                    Ok(slot) => SlotListEntry {
                        slot_id: slot.slot_id,
                        display_name: slot.display_name,
                        updated_at_ms: slot.updated_at_ms,
                        error: None,
                    },
                    Err(error) => SlotListEntry {
                        display_name: slot_id.clone(),
                        slot_id,
                        updated_at_ms: 0,
                        error: Some(error.to_string()),
                    },
                }
            })
            .collect())
    }

    pub fn create(&self, input: CreateSlotInput) -> Result<SlotListEntry> {
        validate_input(&input)?;
        fs::create_dir_all(&self.slot_directory)?;
        let slot_id = Uuid::new_v4().to_string();
        let destination = self.slot_directory.join(format!("{slot_id}.sqlite3"));
        self.create_at(&destination, &slot_id, current_time_ms()?, input)
    }

    pub fn create_at(
        &self,
        destination: &Path,
        slot_id: &str,
        updated_at_ms: i64,
        input: CreateSlotInput,
    ) -> Result<SlotListEntry> {
        validate_slot_id(slot_id)?;
        validate_input(&input)?;
        if destination.extension().and_then(|value| value.to_str()) != Some("sqlite3") {
            return Err(SaveStoreError::InvalidDestinationExtension);
        }
        if destination.file_stem().and_then(|value| value.to_str()) != Some(slot_id) {
            return Err(SaveStoreError::DestinationStemMismatch);
        }
        if destination.exists() {
            return Err(SaveStoreError::DestinationExists);
        }

        let parent = destination
            .parent()
            .ok_or(SaveStoreError::InvalidDestinationExtension)?;
        fs::create_dir_all(parent)?;
        let temporary = parent.join(format!(".{slot_id}.{}.tmp", Uuid::new_v4()));
        let result = create_database(&temporary, slot_id, updated_at_ms, &input);
        if let Err(error) = result {
            let _ = fs::remove_file(&temporary);
            return Err(error);
        }
        if let Err(error) = fs::rename(&temporary, destination) {
            let _ = fs::remove_file(&temporary);
            return Err(error.into());
        }

        Ok(SlotListEntry {
            slot_id: slot_id.to_owned(),
            display_name: input.display_name,
            updated_at_ms,
            error: None,
        })
    }

    pub fn load(&self, slot_id: &str) -> Result<LoadedSlot> {
        let path = self.existing_slot_path(slot_id)?;
        let connection = open_connection(&path, false)?;
        validate_database(&connection)?;

        let (stored_slot_id, display_name, updated_at_ms) = connection
            .query_row(
                "SELECT slot_id, display_name, updated_at_ms FROM metadata WHERE singleton = 1",
                [],
                |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?)),
            )
            .map_err(|_| SaveStoreError::InvalidStructure)?;
        if stored_slot_id != slot_id || table_row_count(&connection, "metadata")? != 1 {
            return Err(SaveStoreError::InvalidStructure);
        }

        let camera = connection
            .query_row(
                "SELECT x, y, z, yaw, pitch FROM camera WHERE singleton = 1",
                [],
                |row| {
                    Ok(CameraRecord {
                        x: row.get(0)?,
                        y: row.get(1)?,
                        z: row.get(2)?,
                        yaw: row.get(3)?,
                        pitch: row.get(4)?,
                    })
                },
            )
            .map_err(|_| SaveStoreError::InvalidStructure)?;
        if table_row_count(&connection, "camera")? != 1 {
            return Err(SaveStoreError::InvalidStructure);
        }
        validate_camera(&camera)?;

        let diagrams = query_diagrams(&connection)?;
        let trees = query_trees(&connection)?;
        for tree in &trees {
            validate_tree_numbers(tree.x, tree.z, tree.yaw)?;
        }

        Ok(LoadedSlot {
            slot_id: stored_slot_id,
            display_name,
            updated_at_ms,
            camera,
            trees,
            diagrams,
        })
    }

    pub fn update_tree(&self, slot_id: &str, update: TreeUpdate) -> Result<i64> {
        validate_tree_numbers(update.x, update.z, update.yaw)?;
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let diagram_key = intern_diagram(&transaction, &update.diagram_json)?;
        let changed = transaction.execute(
            "UPDATE trees SET diagram_key = ?1, x = ?2, z = ?3, yaw = ?4 WHERE tree_id = ?5",
            params![diagram_key, update.x, update.z, update.yaw, update.tree_id],
        )?;
        if changed != 1 {
            return Err(SaveStoreError::TreeNotFound(update.tree_id));
        }
        update_timestamp(&transaction)?;
        transaction.commit()?;
        Ok(diagram_key)
    }

    pub fn update_camera(&self, slot_id: &str, camera: CameraRecord) -> Result<()> {
        validate_camera(&camera)?;
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let changed = transaction.execute(
            "UPDATE camera SET x = ?1, y = ?2, z = ?3, yaw = ?4, pitch = ?5 WHERE singleton = 1",
            params![camera.x, camera.y, camera.z, camera.yaw, camera.pitch],
        )?;
        if changed != 1 {
            return Err(SaveStoreError::InvalidStructure);
        }
        update_timestamp(&transaction)?;
        transaction.commit()?;
        Ok(())
    }

    fn existing_slot_path(&self, slot_id: &str) -> Result<PathBuf> {
        validate_slot_id(slot_id)?;
        let path = self.slot_directory.join(format!("{slot_id}.sqlite3"));
        match fs::symlink_metadata(&path) {
            Ok(metadata) if metadata.file_type().is_file() => Ok(path),
            Ok(_) => Err(SaveStoreError::SlotNotFound(slot_id.to_owned())),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                Err(SaveStoreError::SlotNotFound(slot_id.to_owned()))
            }
            Err(error) => Err(error.into()),
        }
    }
}

fn create_database(
    path: &Path,
    slot_id: &str,
    updated_at_ms: i64,
    input: &CreateSlotInput,
) -> Result<()> {
    let mut connection = Connection::open_with_flags(
        path,
        OpenFlags::SQLITE_OPEN_READ_WRITE | OpenFlags::SQLITE_OPEN_CREATE,
    )?;
    connection.execute_batch("PRAGMA foreign_keys = ON;")?;
    let transaction = connection.transaction()?;
    transaction.execute_batch(SCHEMA)?;
    transaction.execute(
        "INSERT INTO metadata(singleton, slot_id, display_name, updated_at_ms) VALUES (1, ?1, ?2, ?3)",
        params![slot_id, input.display_name, updated_at_ms],
    )?;
    transaction.execute(
        "INSERT INTO camera(singleton, x, y, z, yaw, pitch) VALUES (1, ?1, ?2, ?3, ?4, ?5)",
        params![
            input.camera.x,
            input.camera.y,
            input.camera.z,
            input.camera.yaw,
            input.camera.pitch
        ],
    )?;
    for tree in &input.trees {
        let diagram_key = intern_diagram(&transaction, &tree.diagram_json)?;
        transaction.execute(
            "INSERT INTO trees(tree_id, diagram_key, x, z, yaw) VALUES (?1, ?2, ?3, ?4, ?5)",
            params![tree.tree_id, diagram_key, tree.x, tree.z, tree.yaw],
        )?;
    }
    transaction.commit()?;
    Ok(())
}

fn open_connection(path: &Path, writable: bool) -> Result<Connection> {
    let flags = if writable {
        OpenFlags::SQLITE_OPEN_READ_WRITE
    } else {
        OpenFlags::SQLITE_OPEN_READ_ONLY
    };
    let connection = Connection::open_with_flags(path, flags)?;
    connection.execute_batch("PRAGMA foreign_keys = ON;")?;
    Ok(connection)
}

fn intern_diagram(transaction: &Transaction<'_>, json: &str) -> rusqlite::Result<i64> {
    transaction.execute(
        "INSERT OR IGNORE INTO diagrams(diagram_json) VALUES (?1)",
        [json],
    )?;
    transaction.query_row(
        "SELECT diagram_key FROM diagrams WHERE diagram_json COLLATE BINARY = ?1 COLLATE BINARY",
        [json],
        |row| row.get(0),
    )
}

fn query_diagrams(connection: &Connection) -> Result<Vec<DiagramRecord>> {
    let mut statement = connection
        .prepare("SELECT diagram_key, diagram_json FROM diagrams ORDER BY diagram_key")?;
    let rows = statement.query_map([], |row| {
        Ok(DiagramRecord {
            diagram_key: row.get(0)?,
            diagram_json: row.get(1)?,
        })
    })?;
    Ok(rows.collect::<rusqlite::Result<Vec<_>>>()?)
}

fn query_trees(connection: &Connection) -> Result<Vec<TreeRecord>> {
    let mut statement =
        connection.prepare("SELECT tree_id, diagram_key, x, z, yaw FROM trees ORDER BY tree_id")?;
    let rows = statement.query_map([], |row| {
        Ok(TreeRecord {
            tree_id: row.get(0)?,
            diagram_key: row.get(1)?,
            x: row.get(2)?,
            z: row.get(3)?,
            yaw: row.get(4)?,
        })
    })?;
    Ok(rows.collect::<rusqlite::Result<Vec<_>>>()?)
}

fn validate_input(input: &CreateSlotInput) -> Result<()> {
    validate_camera(&input.camera)?;
    for tree in &input.trees {
        validate_tree_numbers(tree.x, tree.z, tree.yaw)?;
    }
    Ok(())
}

fn validate_camera(camera: &CameraRecord) -> Result<()> {
    if [camera.x, camera.y, camera.z, camera.yaw, camera.pitch]
        .into_iter()
        .all(f64::is_finite)
    {
        Ok(())
    } else {
        Err(SaveStoreError::NonFiniteCamera)
    }
}

fn validate_tree_numbers(x: f64, z: f64, yaw: f64) -> Result<()> {
    if [x, z, yaw].into_iter().all(f64::is_finite) {
        Ok(())
    } else {
        Err(SaveStoreError::NonFiniteTree)
    }
}

fn validate_slot_id(slot_id: &str) -> Result<()> {
    if (1..=64).contains(&slot_id.len())
        && slot_id
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-')
    {
        Ok(())
    } else {
        Err(SaveStoreError::InvalidSlotId)
    }
}

fn current_time_ms() -> Result<i64> {
    let millis = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| SaveStoreError::InvalidSystemClock)?
        .as_millis();
    i64::try_from(millis).map_err(|_| SaveStoreError::TimestampOverflow)
}

fn update_timestamp(transaction: &Transaction<'_>) -> Result<()> {
    let previous: i64 = transaction.query_row(
        "SELECT updated_at_ms FROM metadata WHERE singleton = 1",
        [],
        |row| row.get(0),
    )?;
    let timestamp = current_time_ms()?.max(
        previous
            .checked_add(1)
            .ok_or(SaveStoreError::TimestampOverflow)?,
    );
    if transaction.execute(
        "UPDATE metadata SET updated_at_ms = ?1 WHERE singleton = 1",
        [timestamp],
    )? != 1
    {
        return Err(SaveStoreError::InvalidStructure);
    }
    Ok(())
}

#[derive(Debug)]
struct Column {
    name: String,
    declared_type: String,
    not_null: bool,
    primary_key_position: i64,
}

#[derive(PartialEq)]
enum Affinity {
    Integer,
    Text,
    Real,
    Numeric,
    Blob,
}

fn column(name: &str, declared_type: &str, not_null: bool, primary_key_position: i64) -> Column {
    Column {
        name: name.to_owned(),
        declared_type: declared_type.to_owned(),
        not_null,
        primary_key_position,
    }
}

fn validate_database(connection: &Connection) -> Result<()> {
    validate_database_inner(connection).map_err(|_| SaveStoreError::InvalidStructure)
}

fn validate_database_inner(connection: &Connection) -> rusqlite::Result<()> {
    validate_no_required_table_triggers(connection)?;
    validate_required_columns(
        connection,
        "metadata",
        vec![
            column("singleton", "INTEGER", false, 1),
            column("slot_id", "TEXT", true, 0),
            column("display_name", "TEXT", true, 0),
            column("updated_at_ms", "INTEGER", true, 0),
        ],
    )?;
    validate_required_columns(
        connection,
        "camera",
        vec![
            column("singleton", "INTEGER", false, 1),
            column("x", "REAL", true, 0),
            column("y", "REAL", true, 0),
            column("z", "REAL", true, 0),
            column("yaw", "REAL", true, 0),
            column("pitch", "REAL", true, 0),
        ],
    )?;
    validate_required_columns(
        connection,
        "diagrams",
        vec![
            column("diagram_key", "INTEGER", false, 1),
            column("diagram_json", "TEXT", true, 0),
        ],
    )?;
    validate_required_columns(
        connection,
        "trees",
        vec![
            column("tree_id", "TEXT", false, 1),
            column("diagram_key", "INTEGER", true, 0),
            column("x", "REAL", true, 0),
            column("z", "REAL", true, 0),
            column("yaw", "REAL", true, 0),
        ],
    )?;

    if !has_unique_key(connection, "metadata", &["slot_id"], false)?
        || !has_unique_key(connection, "diagrams", &["diagram_json"], true)?
    {
        return Err(rusqlite::Error::InvalidQuery);
    }
    validate_foreign_keys(connection)?;

    let integrity: String = connection.query_row("PRAGMA integrity_check", [], |row| row.get(0))?;
    if integrity != "ok" {
        return Err(rusqlite::Error::InvalidQuery);
    }
    let foreign_key_failure = connection
        .query_row("PRAGMA foreign_key_check", [], |_| Ok(()))
        .optional()?;
    if foreign_key_failure.is_some() {
        return Err(rusqlite::Error::InvalidQuery);
    }
    Ok(())
}

fn validate_required_columns(
    connection: &Connection,
    table: &str,
    expected: Vec<Column>,
) -> rusqlite::Result<()> {
    let mut statement = connection.prepare(&format!("PRAGMA table_info('{table}')"))?;
    let actual = statement
        .query_map([], |row| {
            Ok(Column {
                name: row.get(1)?,
                declared_type: row.get(2)?,
                not_null: row.get::<_, i64>(3)? != 0,
                primary_key_position: row.get(5)?,
            })
        })?
        .collect::<rusqlite::Result<Vec<_>>>()?;
    for required in expected {
        let Some(actual) = actual.iter().find(|actual| actual.name == required.name) else {
            return Err(rusqlite::Error::InvalidQuery);
        };
        if sqlite_affinity(&actual.declared_type) != sqlite_affinity(&required.declared_type)
            || actual.not_null != required.not_null
            || actual.primary_key_position != required.primary_key_position
        {
            return Err(rusqlite::Error::InvalidQuery);
        }
    }
    Ok(())
}

fn sqlite_affinity(declared_type: &str) -> Affinity {
    let declared_type = declared_type.to_ascii_uppercase();
    if declared_type.contains("INT") {
        Affinity::Integer
    } else if declared_type.contains("CHAR")
        || declared_type.contains("CLOB")
        || declared_type.contains("TEXT")
    {
        Affinity::Text
    } else if declared_type.is_empty() || declared_type.contains("BLOB") {
        Affinity::Blob
    } else if declared_type.contains("REAL")
        || declared_type.contains("FLOA")
        || declared_type.contains("DOUB")
    {
        Affinity::Real
    } else {
        Affinity::Numeric
    }
}

fn validate_update_safety(connection: &Connection) -> Result<()> {
    validate_no_required_table_triggers(connection).map_err(|_| SaveStoreError::InvalidStructure)
}

fn validate_no_required_table_triggers(connection: &Connection) -> rusqlite::Result<()> {
    let active_trigger: bool = connection.query_row(
        "SELECT EXISTS(
           SELECT 1 FROM sqlite_schema
           WHERE type = 'trigger'
             AND tbl_name IN ('metadata', 'camera', 'diagrams', 'trees')
         )",
        [],
        |row| row.get(0),
    )?;
    if active_trigger {
        Err(rusqlite::Error::InvalidQuery)
    } else {
        Ok(())
    }
}

fn has_unique_key(
    connection: &Connection,
    table: &str,
    expected_columns: &[&str],
    require_binary_collation: bool,
) -> rusqlite::Result<bool> {
    let mut statement = connection.prepare(&format!("PRAGMA index_list('{table}')"))?;
    let indexes = statement
        .query_map([], |row| {
            Ok((
                row.get::<_, String>(1)?,
                row.get::<_, i64>(2)? != 0,
                row.get::<_, i64>(4)? != 0,
            ))
        })?
        .collect::<rusqlite::Result<Vec<_>>>()?;

    for (name, unique, partial) in indexes {
        if !unique || partial {
            continue;
        }
        let mut column_statement = connection.prepare(&format!(
            "PRAGMA index_xinfo('{}')",
            name.replace('\'', "''")
        ))?;
        let columns = column_statement
            .query_map([], |row| {
                Ok((
                    row.get::<_, i64>(0)?,
                    row.get::<_, Option<String>>(2)?,
                    row.get::<_, String>(4)?,
                    row.get::<_, i64>(5)? != 0,
                ))
            })?
            .collect::<rusqlite::Result<Vec<_>>>()?;
        let key_columns = columns
            .iter()
            .filter(|(_, _, _, is_key)| *is_key)
            .collect::<Vec<_>>();
        if key_columns.len() != expected_columns.len()
            || key_columns
                .iter()
                .enumerate()
                .any(|(position, (sequence, name, collation, _))| {
                    *sequence != position as i64
                        || name.as_deref() != Some(expected_columns[position])
                        || (require_binary_collation && collation != "BINARY")
                })
        {
            continue;
        }
        return Ok(true);
    }
    Ok(false)
}

fn validate_foreign_keys(connection: &Connection) -> rusqlite::Result<()> {
    let mut statement = connection.prepare("PRAGMA foreign_key_list('trees')")?;
    let actual = statement
        .query_map([], |row| {
            Ok((
                row.get::<_, String>(2)?,
                row.get::<_, String>(3)?,
                row.get::<_, String>(4)?,
            ))
        })?
        .collect::<rusqlite::Result<Vec<_>>>()?;
    if actual.iter().any(|(table, from, to)| {
        table == "diagrams" && from == "diagram_key" && to == "diagram_key"
    }) {
        Ok(())
    } else {
        Err(rusqlite::Error::InvalidQuery)
    }
}

fn table_row_count(connection: &Connection, table: &str) -> Result<i64> {
    Ok(
        connection.query_row(&format!("SELECT COUNT(*) FROM {table}"), [], |row| {
            row.get(0)
        })?,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use rusqlite::Connection;
    use std::path::Path;

    const BLANK: &str = r#"{"regions":[],"nodes":[],"wires":[]}"#;
    const DOUBLE_CUT: &str = r#"{"regions":[{"id":"cut"}],"nodes":[],"wires":[]}"#;

    fn camera() -> CameraRecord {
        CameraRecord {
            x: 1.0,
            y: 2.0,
            z: 3.0,
            yaw: 0.25,
            pitch: -0.5,
        }
    }

    fn tree(tree_id: &str, diagram_json: &str) -> TreeUpdate {
        TreeUpdate {
            tree_id: tree_id.into(),
            diagram_json: diagram_json.into(),
            x: 0.0,
            z: 0.0,
            yaw: 0.0,
        }
    }

    fn basic_input() -> CreateSlotInput {
        CreateSlotInput {
            display_name: "First Orchard".into(),
            camera: camera(),
            trees: vec![tree("a", BLANK), tree("b", BLANK)],
        }
    }

    fn assert_invalid_list_entry(root: &Path, filename: &str) {
        let store = SaveStore::new(root.to_path_buf());
        let entries = store.list().unwrap();
        let entry = entries
            .iter()
            .find(|entry| entry.slot_id == filename.trim_end_matches(".sqlite3"))
            .unwrap();
        assert_eq!(
            entry.error.as_deref(),
            Some("save database has an invalid structure")
        );
    }

    #[test]
    fn creates_loads_and_updates_only_one_tree() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot = store.create(basic_input()).unwrap();

        let before = store.load(&slot.slot_id).unwrap();
        assert_eq!(before.diagrams.len(), 1);
        let changed_key = store
            .update_tree(
                &slot.slot_id,
                TreeUpdate {
                    tree_id: "a".into(),
                    diagram_json: DOUBLE_CUT.into(),
                    x: 4.0,
                    z: 5.0,
                    yaw: 0.75,
                },
            )
            .unwrap();
        let after = store.load(&slot.slot_id).unwrap();

        assert_ne!(changed_key, before.trees[0].diagram_key);
        assert_eq!(
            after.trees.iter().find(|tree| tree.tree_id == "a"),
            Some(&TreeRecord {
                tree_id: "a".into(),
                diagram_key: changed_key,
                x: 4.0,
                z: 5.0,
                yaw: 0.75,
            })
        );
        assert_eq!(
            after
                .diagrams
                .iter()
                .find(|diagram| diagram.diagram_key == changed_key),
            Some(&DiagramRecord {
                diagram_key: changed_key,
                diagram_json: DOUBLE_CUT.into(),
            })
        );
        assert_eq!(
            after
                .trees
                .iter()
                .find(|tree| tree.tree_id == "b")
                .unwrap()
                .diagram_key,
            before
                .trees
                .iter()
                .find(|tree| tree.tree_id == "b")
                .unwrap()
                .diagram_key
        );
        assert_eq!(after.camera, before.camera);
        assert_eq!(after.diagrams.len(), 2);
        assert!(after.updated_at_ms > before.updated_at_ms);
    }

    #[test]
    fn loads_an_equivalent_current_schema_with_an_inert_view() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("equivalent.sqlite3");
        let connection = Connection::open(&path).unwrap();
        connection
            .execute_batch(
                "CREATE TABLE metadata(
                    singleton INTEGER PRIMARY KEY,
                    slot_id TEXT UNIQUE NOT NULL,
                    display_name TEXT NOT NULL,
                    updated_at_ms INTEGER NOT NULL
                 );
                 CREATE TABLE camera(singleton INTEGER PRIMARY KEY,
                    x REAL NOT NULL,y REAL NOT NULL,z REAL NOT NULL,yaw REAL NOT NULL,pitch REAL NOT NULL);
                 CREATE TABLE diagrams(diagram_key INTEGER PRIMARY KEY,diagram_json TEXT UNIQUE NOT NULL);
                 CREATE TABLE trees(tree_id TEXT PRIMARY KEY,diagram_key INTEGER NOT NULL REFERENCES diagrams(diagram_key),
                    x REAL NOT NULL,z REAL NOT NULL,yaw REAL NOT NULL);
                 CREATE VIEW tree_names AS SELECT tree_id FROM trees;
                 INSERT INTO metadata VALUES(1, 'equivalent', 'Equivalent', 12);
                 INSERT INTO camera VALUES(1, 1, 2, 3, .25, -.5);
                 INSERT INTO diagrams VALUES(7, '{\"regions\":[],\"nodes\":[],\"wires\":[]}');
                 INSERT INTO trees VALUES('tree-a', 7, 4, 5, .75);",
            )
            .unwrap();

        let loaded = SaveStore::new(temp.path().to_path_buf())
            .load("equivalent")
            .unwrap();

        assert_eq!(loaded.display_name, "Equivalent");
        assert_eq!(
            loaded.trees,
            vec![TreeRecord {
                tree_id: "tree-a".into(),
                diagram_key: 7,
                x: 4.0,
                z: 5.0,
                yaw: 0.75,
            }]
        );
        assert_eq!(
            loaded.diagrams,
            vec![DiagramRecord {
                diagram_key: 7,
                diagram_json: BLANK.into()
            }]
        );
    }

    #[test]
    fn loads_an_equivalent_schema_with_affinity_equivalent_declared_types() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("affinity.sqlite3");
        let connection = Connection::open(&path).unwrap();
        connection
            .execute_batch(
                &SCHEMA
                    .replace("INTEGER", "int")
                    .replace("TEXT", "varchar(256)")
                    .replace("REAL", "double precision"),
            )
            .unwrap();
        connection
            .execute_batch(
                "INSERT INTO metadata VALUES(1, 'affinity', 'Affinity', 12);
                 INSERT INTO camera VALUES(1, 1, 2, 3, .25, -.5);
                 INSERT INTO diagrams VALUES(7, '{\"regions\":[],\"nodes\":[],\"wires\":[]}');
                 INSERT INTO trees VALUES('tree-a', 7, 4, 5, .75);",
            )
            .unwrap();

        let loaded = SaveStore::new(temp.path().to_path_buf())
            .load("affinity")
            .unwrap();

        assert_eq!(loaded.slot_id, "affinity");
        assert_eq!(loaded.trees.len(), 1);
    }

    #[test]
    fn rejects_required_table_triggers_before_load_or_update() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot = store.create(basic_input()).unwrap();
        let before = store.load(&slot.slot_id).unwrap();
        let path = temp.path().join(format!("{}.sqlite3", slot.slot_id));
        let connection = Connection::open(&path).unwrap();
        connection
            .execute_batch(
                "CREATE TRIGGER mutate_camera AFTER UPDATE ON trees
                 BEGIN UPDATE camera SET x = x + 1; END;",
            )
            .unwrap();

        assert!(matches!(
            store.load(&slot.slot_id),
            Err(SaveStoreError::InvalidStructure)
        ));
        assert!(matches!(
            store.update_tree(&slot.slot_id, tree("a", DOUBLE_CUT)),
            Err(SaveStoreError::InvalidStructure)
        ));

        connection
            .execute_batch("DROP TRIGGER mutate_camera;")
            .unwrap();
        assert_eq!(store.load(&slot.slot_id).unwrap(), before);
    }

    #[test]
    fn rejects_missing_required_schema_semantics() {
        let temp = tempfile::tempdir().unwrap();
        let missing_column = temp.path().join("missing-column.sqlite3");
        Connection::open(&missing_column)
            .unwrap()
            .execute_batch(&SCHEMA.replace("pitch REAL NOT NULL", "tilt REAL NOT NULL"))
            .unwrap();

        let missing_foreign_key = temp.path().join("missing-foreign-key.sqlite3");
        Connection::open(&missing_foreign_key)
            .unwrap()
            .execute_batch(&SCHEMA.replace(
                "diagram_key INTEGER NOT NULL REFERENCES diagrams(diagram_key)",
                "diagram_key INTEGER NOT NULL",
            ))
            .unwrap();

        assert_invalid_list_entry(temp.path(), "missing-column.sqlite3");
        assert_invalid_list_entry(temp.path(), "missing-foreign-key.sqlite3");
    }

    #[test]
    fn rejects_dangling_references_and_non_finite_values() {
        let temp = tempfile::tempdir().unwrap();
        let dangling = temp.path().join("dangling.sqlite3");
        let connection = Connection::open(&dangling).unwrap();
        connection.execute_batch(SCHEMA).unwrap();
        connection
            .execute_batch(
                "PRAGMA foreign_keys = OFF;
             INSERT INTO metadata VALUES(1, 'dangling', 'Dangling', 0);
             INSERT INTO camera VALUES(1, 0, 0, 0, 0, 0);
             INSERT INTO trees VALUES('tree-a', 9, 0, 0, 0);",
            )
            .unwrap();

        let non_finite = temp.path().join("non-finite.sqlite3");
        let connection = Connection::open(&non_finite).unwrap();
        connection.execute_batch(SCHEMA).unwrap();
        connection
            .execute_batch(
                "INSERT INTO metadata VALUES(1, 'non-finite', 'Non finite', 0);
             INSERT INTO camera VALUES(1, 0, 0, 0, 0, 0);
             INSERT INTO diagrams VALUES(1, '{\"regions\":[],\"nodes\":[],\"wires\":[]}');
             INSERT INTO trees VALUES('tree-a', 1, 1e999, 0, 0);",
            )
            .unwrap();

        for slot_id in ["dangling", "non-finite"] {
            assert!(
                SaveStore::new(temp.path().to_path_buf())
                    .load(slot_id)
                    .is_err(),
                "{slot_id}"
            );
        }
    }

    #[test]
    fn stores_and_loads_opaque_diagram_json_unchanged() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot = store
            .create(CreateSlotInput {
                display_name: "Opaque diagram".into(),
                camera: camera(),
                trees: vec![tree("tree-a", r#""not a diagram""#)],
            })
            .unwrap();

        let loaded = store.load(&slot.slot_id).unwrap();

        assert_eq!(
            loaded.diagrams,
            vec![DiagramRecord {
                diagram_key: loaded.trees[0].diagram_key,
                diagram_json: r#""not a diagram""#.into(),
            }]
        );
    }

    #[test]
    fn shares_only_byte_identical_diagram_json() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot = store
            .create(CreateSlotInput {
                display_name: "Exact bytes".into(),
                camera: camera(),
                trees: vec![
                    tree("a", BLANK),
                    tree("b", BLANK),
                    tree("c", r#"{ "regions":[],"nodes":[],"wires":[]}"#),
                ],
            })
            .unwrap();

        let loaded = store.load(&slot.slot_id).unwrap();
        assert_eq!(loaded.diagrams.len(), 2);
        assert_eq!(loaded.trees[0].diagram_key, loaded.trees[1].diagram_key);
        assert_ne!(loaded.trees[0].diagram_key, loaded.trees[2].diagram_key);
    }

    #[test]
    fn rejects_invalid_and_unknown_slot_ids_before_opening_a_path() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());

        assert_eq!(
            store.load("../outside").unwrap_err().to_string(),
            "invalid slot id"
        );
        assert_eq!(
            store.load("missing").unwrap_err().to_string(),
            "save slot 'missing' was not found"
        );
        assert!(!temp.path().join("missing.sqlite3").exists());
    }

    #[test]
    fn an_unknown_tree_leaves_the_loaded_world_unchanged() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot = store.create(basic_input()).unwrap();
        let before = store.load(&slot.slot_id).unwrap();

        assert_eq!(
            store
                .update_tree(&slot.slot_id, tree("missing", DOUBLE_CUT))
                .unwrap_err()
                .to_string(),
            "tree 'missing' was not found"
        );

        let after = store.load(&slot.slot_id).unwrap();
        assert_eq!(after, before);
    }

    #[test]
    fn rejects_non_finite_numbers_without_changing_the_slot() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot = store.create(basic_input()).unwrap();
        let before = store.load(&slot.slot_id).unwrap();

        let mut invalid_tree = tree("a", DOUBLE_CUT);
        invalid_tree.yaw = f64::INFINITY;
        assert_eq!(
            store
                .update_tree(&slot.slot_id, invalid_tree)
                .unwrap_err()
                .to_string(),
            "tree coordinates must be finite"
        );

        let mut invalid_camera = camera();
        invalid_camera.pitch = f64::NAN;
        assert_eq!(
            store
                .update_camera(&slot.slot_id, invalid_camera)
                .unwrap_err()
                .to_string(),
            "camera coordinates must be finite"
        );

        assert_eq!(store.load(&slot.slot_id).unwrap(), before);
    }

    #[test]
    fn camera_update_changes_only_the_durable_camera() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot = store.create(basic_input()).unwrap();
        let before = store.load(&slot.slot_id).unwrap();
        let updated_camera = CameraRecord {
            x: 10.0,
            y: 11.0,
            z: 12.0,
            yaw: 1.0,
            pitch: -1.0,
        };

        store
            .update_camera(&slot.slot_id, updated_camera.clone())
            .unwrap();

        let after = store.load(&slot.slot_id).unwrap();
        assert_eq!(after.camera, updated_camera);
        assert_eq!(after.trees, before.trees);
        assert_eq!(after.diagrams, before.diagrams);
        assert!(after.updated_at_ms > before.updated_at_ms);
    }

    #[test]
    fn create_at_writes_an_ordinary_file_loadable_by_slot_id() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let destination = temp.path().join("fixture-1.sqlite3");

        store
            .create_at(&destination, "fixture-1", 1234, basic_input())
            .unwrap();

        let loaded = store.load("fixture-1").unwrap();
        assert_eq!(loaded.slot_id, "fixture-1");
        assert_eq!(loaded.display_name, "First Orchard");
        assert_eq!(loaded.updated_at_ms, 1234);
        assert_eq!(loaded.trees.len(), 2);
    }

    #[test]
    fn create_at_requires_the_slot_id_to_match_the_file_stem() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let destination = temp.path().join("fixture-1.sqlite3");

        assert_eq!(
            store
                .create_at(&destination, "different", 1234, basic_input())
                .unwrap_err()
                .to_string(),
            "slot id must match the destination file stem"
        );
        assert!(!destination.exists());
    }

    #[test]
    fn list_ignores_non_database_entries() {
        let temp = tempfile::tempdir().unwrap();
        std::fs::write(temp.path().join("notes.txt"), "not a save").unwrap();
        std::fs::create_dir(temp.path().join("directory.sqlite3")).unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());

        assert!(store.list().unwrap().is_empty());
    }
}
