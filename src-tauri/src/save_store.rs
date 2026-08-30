use rusqlite::{params, Connection, ErrorCode, OpenFlags, OptionalExtension, Transaction};
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
CREATE TABLE progress (
  singleton INTEGER PRIMARY KEY CHECK (singleton = 1),
  reputation INTEGER NOT NULL CHECK (reputation >= 0),
  tutorials_enabled BOOLEAN NOT NULL CHECK (tutorials_enabled IN (0, 1))
);
CREATE TABLE tutorial_milestones (
  milestone_id TEXT PRIMARY KEY
);
CREATE TABLE acquired_tools (
  tool_id TEXT PRIMARY KEY
);
CREATE TABLE orders (
  order_id TEXT PRIMARY KEY,
  state TEXT NOT NULL CHECK (state IN ('pending', 'accepted', 'completed')),
  pot_x REAL,
  pot_z REAL,
  pot_yaw REAL,
  CHECK (
    (state = 'accepted' AND pot_x IS NOT NULL AND pot_z IS NOT NULL AND pot_yaw IS NOT NULL)
    OR
    (state IN ('pending', 'completed') AND pot_x IS NULL AND pot_z IS NULL AND pot_yaw IS NULL)
  )
);
";

const MAX_REPUTATION: i64 = 9_007_199_254_740_991;

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
pub struct PotPlacementRecord {
    pub x: f64,
    pub z: f64,
    pub yaw: f64,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum OrderStatus {
    Pending,
    Accepted,
    Completed,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct OrderRecord {
    pub order_id: String,
    pub state: OrderStatus,
    pub pot: Option<PotPlacementRecord>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct CreateSlotInput {
    pub display_name: String,
    pub camera: CameraRecord,
    pub trees: Vec<TreeUpdate>,
    pub reputation: i64,
    pub tutorials_enabled: bool,
    pub completed_tutorial_milestones: Vec<String>,
    pub acquired_tool_ids: Vec<String>,
    pub orders: Vec<OrderRecord>,
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
    pub reputation: i64,
    pub tutorials_enabled: bool,
    pub completed_tutorial_milestones: Vec<String>,
    pub acquired_tool_ids: Vec<String>,
    pub orders: Vec<OrderRecord>,
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
    #[error("tree '{0}' conflicts with its existing saved value")]
    TreeConflict(String),
    #[error("order '{0}' was not found")]
    OrderNotFound(String),
    #[error("order '{0}' cannot make the requested transition")]
    OrderTransitionConflict(String),
    #[error("camera coordinates must be finite")]
    NonFiniteCamera,
    #[error("tree coordinates must be finite")]
    NonFiniteTree,
    #[error("pot placement coordinates must be finite")]
    NonFinitePotPlacement,
    #[error("order reward must be nonnegative")]
    NegativeOrderReward,
    #[error("identifier must not be blank")]
    BlankIdentifier,
    #[error("reputation cannot be increased")]
    ReputationOverflow,
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
        let (reputation, tutorials_enabled) = connection
            .query_row(
                "SELECT reputation, tutorials_enabled FROM progress WHERE singleton = 1",
                [],
                |row| Ok((row.get(0)?, row.get::<_, bool>(1)?)),
            )
            .map_err(|_| SaveStoreError::InvalidStructure)?;
        if table_row_count(&connection, "progress")? != 1
            || !(0..=MAX_REPUTATION).contains(&reputation)
        {
            return Err(SaveStoreError::InvalidStructure);
        }
        let completed_tutorial_milestones =
            query_identifier_table(&connection, "tutorial_milestones", "milestone_id")
                .map_err(|_| SaveStoreError::InvalidStructure)?;
        let acquired_tool_ids = query_identifier_table(&connection, "acquired_tools", "tool_id")
            .map_err(|_| SaveStoreError::InvalidStructure)?;
        let orders = query_orders(&connection)?;

        Ok(LoadedSlot {
            slot_id: stored_slot_id,
            display_name,
            updated_at_ms,
            camera,
            trees,
            diagrams,
            reputation,
            tutorials_enabled,
            completed_tutorial_milestones,
            acquired_tool_ids,
            orders,
        })
    }

    pub fn insert_tree(&self, slot_id: &str, update: TreeUpdate) -> Result<i64> {
        validate_tree_numbers(update.x, update.z, update.yaw)?;
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let existing = transaction
            .query_row(
                "SELECT trees.diagram_key, diagrams.diagram_json, trees.x, trees.z, trees.yaw
                 FROM trees JOIN diagrams USING (diagram_key)
                 WHERE trees.tree_id = ?1",
                [&update.tree_id],
                |row| {
                    Ok((
                        row.get::<_, i64>(0)?,
                        row.get::<_, String>(1)?,
                        row.get::<_, f64>(2)?,
                        row.get::<_, f64>(3)?,
                        row.get::<_, f64>(4)?,
                    ))
                },
            )
            .optional()?;
        if let Some((diagram_key, diagram_json, x, z, yaw)) = existing {
            if diagram_json == update.diagram_json
                && x == update.x
                && z == update.z
                && yaw == update.yaw
            {
                return Ok(diagram_key);
            }
            return Err(SaveStoreError::TreeConflict(update.tree_id));
        }

        let diagram_key = intern_diagram(&transaction, &update.diagram_json)?;
        transaction.execute(
            "INSERT INTO trees(tree_id, diagram_key, x, z, yaw) VALUES (?1, ?2, ?3, ?4, ?5)",
            params![update.tree_id, diagram_key, update.x, update.z, update.yaw],
        )?;
        update_timestamp(&transaction)?;
        transaction.commit()?;
        Ok(diagram_key)
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

    pub fn set_tutorials_enabled(&self, slot_id: &str, enabled: bool) -> Result<()> {
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let changed = transaction.execute(
            "UPDATE progress SET tutorials_enabled = ?1
             WHERE singleton = 1 AND tutorials_enabled != ?1",
            [enabled],
        )?;
        if changed > 1 {
            return Err(SaveStoreError::InvalidStructure);
        }
        if changed == 1 {
            update_timestamp(&transaction)?;
        }
        transaction.commit()?;
        Ok(())
    }

    pub fn complete_tutorial_milestone(&self, slot_id: &str, milestone_id: &str) -> Result<()> {
        validate_identifier(milestone_id)?;
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let inserted = transaction.execute(
            "INSERT INTO tutorial_milestones(milestone_id) VALUES (?1)
             ON CONFLICT DO NOTHING",
            [milestone_id],
        )?;
        if inserted == 1 {
            update_timestamp(&transaction)?;
        }
        transaction.commit()?;
        Ok(())
    }

    pub fn acquire_tool(&self, slot_id: &str, tool_id: &str) -> Result<()> {
        validate_identifier(tool_id)?;
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let inserted = transaction.execute(
            "INSERT INTO acquired_tools(tool_id) VALUES (?1) ON CONFLICT DO NOTHING",
            [tool_id],
        )?;
        if inserted == 1 {
            update_timestamp(&transaction)?;
        }
        transaction.commit()?;
        Ok(())
    }

    pub fn replace_order_ids(&self, slot_id: &str, order_ids: &[String]) -> Result<()> {
        validate_identifiers(order_ids)?;
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let existing_order_ids = {
            let mut statement = transaction.prepare("SELECT order_id FROM orders")?;
            let order_ids = statement
                .query_map([], |row| row.get::<_, String>(0))?
                .collect::<rusqlite::Result<Vec<_>>>()?;
            order_ids
        };
        let requested = order_ids
            .iter()
            .map(String::as_str)
            .collect::<std::collections::HashSet<_>>();
        for existing_order_id in existing_order_ids {
            if !requested.contains(existing_order_id.as_str()) {
                transaction.execute(
                    "DELETE FROM orders WHERE order_id = ?1",
                    [&existing_order_id],
                )?;
            }
        }
        for order_id in order_ids {
            transaction.execute(
                "INSERT INTO orders(order_id, state, pot_x, pot_z, pot_yaw)
                 VALUES (?1, 'pending', NULL, NULL, NULL) ON CONFLICT DO NOTHING",
                [order_id],
            )?;
        }
        update_timestamp(&transaction)?;
        transaction.commit()?;
        Ok(())
    }

    pub fn accept_order(
        &self,
        slot_id: &str,
        order_id: &str,
        pot: PotPlacementRecord,
    ) -> Result<()> {
        validate_pot(&pot)?;
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let changed = transaction.execute(
            "UPDATE orders
             SET state = 'accepted', pot_x = ?1, pot_z = ?2, pot_yaw = ?3
             WHERE order_id = ?4 AND state = 'pending'",
            params![pot.x, pot.z, pot.yaw, order_id],
        )?;
        if changed == 1 {
            update_timestamp(&transaction)?;
            transaction.commit()?;
            return Ok(());
        }

        let current = query_order_state(&transaction, order_id)?;
        match current {
            None => Err(SaveStoreError::OrderNotFound(order_id.to_owned())),
            Some((OrderStatus::Accepted, Some(current_pot))) if current_pot == pot => Ok(()),
            Some(_) => Err(SaveStoreError::OrderTransitionConflict(order_id.to_owned())),
        }
    }

    pub fn abandon_order(&self, slot_id: &str, order_id: &str) -> Result<()> {
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let changed = transaction.execute(
            "UPDATE orders
             SET state = 'pending', pot_x = NULL, pot_z = NULL, pot_yaw = NULL
             WHERE order_id = ?1 AND state = 'accepted'",
            [order_id],
        )?;
        if changed == 1 {
            update_timestamp(&transaction)?;
            transaction.commit()?;
            return Ok(());
        }

        match query_order_state(&transaction, order_id)? {
            None => Err(SaveStoreError::OrderNotFound(order_id.to_owned())),
            Some((OrderStatus::Pending, None)) => Ok(()),
            Some(_) => Err(SaveStoreError::OrderTransitionConflict(order_id.to_owned())),
        }
    }

    pub fn complete_order(&self, slot_id: &str, order_id: &str, reward: i64) -> Result<i64> {
        if reward < 0 {
            return Err(SaveStoreError::NegativeOrderReward);
        }
        let path = self.existing_slot_path(slot_id)?;
        let mut connection = open_connection(&path, true)?;
        validate_update_safety(&connection)?;
        let transaction = connection.transaction()?;
        let changed = transaction.execute(
            "UPDATE orders
             SET state = 'completed', pot_x = NULL, pot_z = NULL, pot_yaw = NULL
             WHERE order_id = ?1 AND state = 'accepted'",
            [order_id],
        )?;
        if changed == 1 {
            let reward_limit = MAX_REPUTATION - reward;
            if transaction.execute(
                "UPDATE progress SET reputation = reputation + ?1
                 WHERE singleton = 1 AND reputation <= ?2",
                params![reward, reward_limit],
            )? != 1
            {
                return Err(SaveStoreError::ReputationOverflow);
            }
            let reputation = query_reputation(&transaction)?;
            update_timestamp(&transaction)?;
            transaction.commit()?;
            return Ok(reputation);
        }

        match query_order_state(&transaction, order_id)? {
            None => Err(SaveStoreError::OrderNotFound(order_id.to_owned())),
            Some((OrderStatus::Completed, None)) => query_reputation(&transaction),
            Some(_) => Err(SaveStoreError::OrderTransitionConflict(order_id.to_owned())),
        }
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
    transaction.execute(
        "INSERT INTO progress(singleton, reputation, tutorials_enabled) VALUES (1, ?1, ?2)",
        params![input.reputation, input.tutorials_enabled],
    )?;
    for milestone_id in &input.completed_tutorial_milestones {
        transaction.execute(
            "INSERT INTO tutorial_milestones(milestone_id) VALUES (?1)",
            [milestone_id],
        )?;
    }
    for tool_id in &input.acquired_tool_ids {
        transaction.execute("INSERT INTO acquired_tools(tool_id) VALUES (?1)", [tool_id])?;
    }
    for order in &input.orders {
        let (state, pot_x, pot_z, pot_yaw) = order_columns(order);
        transaction.execute(
            "INSERT INTO orders(order_id, state, pot_x, pot_z, pot_yaw)
             VALUES (?1, ?2, ?3, ?4, ?5)",
            params![order.order_id, state, pot_x, pot_z, pot_yaw],
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

fn query_orders(connection: &Connection) -> Result<Vec<OrderRecord>> {
    let mut statement = connection
        .prepare("SELECT order_id, state, pot_x, pot_z, pot_yaw FROM orders ORDER BY order_id")?;
    let rows = statement.query_map([], |row| {
        Ok((
            row.get::<_, String>(0)?,
            row.get::<_, String>(1)?,
            row.get::<_, Option<f64>>(2)?,
            row.get::<_, Option<f64>>(3)?,
            row.get::<_, Option<f64>>(4)?,
        ))
    })?;
    let mut orders = Vec::new();
    let mut order_ids = std::collections::HashSet::new();
    for row in rows {
        let (order_id, state, pot_x, pot_z, pot_yaw) = row?;
        if !order_ids.insert(order_id.clone()) {
            return Err(SaveStoreError::InvalidStructure);
        }
        let (state, pot) = decode_order_state(&state, pot_x, pot_z, pot_yaw)?;
        orders.push(OrderRecord {
            order_id,
            state,
            pot,
        });
    }
    Ok(orders)
}

fn query_identifier_table(
    connection: &Connection,
    table: &str,
    id_column: &str,
) -> Result<Vec<String>> {
    let mut statement = connection.prepare(&format!(
        "SELECT {id_column} FROM {table} ORDER BY {id_column}"
    ))?;
    let ids = statement
        .query_map([], |row| row.get::<_, String>(0))?
        .collect::<rusqlite::Result<Vec<_>>>()?;
    validate_identifiers(&ids).map_err(|_| SaveStoreError::InvalidStructure)?;
    Ok(ids)
}

fn query_order_state(
    connection: &Connection,
    order_id: &str,
) -> Result<Option<(OrderStatus, Option<PotPlacementRecord>)>> {
    let row = connection
        .query_row(
            "SELECT state, pot_x, pot_z, pot_yaw FROM orders WHERE order_id = ?1",
            [order_id],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, Option<f64>>(1)?,
                    row.get::<_, Option<f64>>(2)?,
                    row.get::<_, Option<f64>>(3)?,
                ))
            },
        )
        .optional()?;
    row.map(|(state, x, z, yaw)| decode_order_state(&state, x, z, yaw))
        .transpose()
}

fn query_reputation(connection: &Connection) -> Result<i64> {
    let reputation = connection
        .query_row(
            "SELECT reputation FROM progress WHERE singleton = 1",
            [],
            |row| row.get(0),
        )
        .map_err(|_| SaveStoreError::InvalidStructure)?;
    if !(0..=MAX_REPUTATION).contains(&reputation) {
        Err(SaveStoreError::InvalidStructure)
    } else {
        Ok(reputation)
    }
}

fn decode_order_state(
    state: &str,
    pot_x: Option<f64>,
    pot_z: Option<f64>,
    pot_yaw: Option<f64>,
) -> Result<(OrderStatus, Option<PotPlacementRecord>)> {
    match (state, pot_x, pot_z, pot_yaw) {
        ("pending", None, None, None) => Ok((OrderStatus::Pending, None)),
        ("completed", None, None, None) => Ok((OrderStatus::Completed, None)),
        ("accepted", Some(x), Some(z), Some(yaw)) => {
            let pot = PotPlacementRecord { x, z, yaw };
            validate_pot(&pot).map_err(|_| SaveStoreError::InvalidStructure)?;
            Ok((OrderStatus::Accepted, Some(pot)))
        }
        _ => Err(SaveStoreError::InvalidStructure),
    }
}

fn order_columns(order: &OrderRecord) -> (&'static str, Option<f64>, Option<f64>, Option<f64>) {
    match (&order.state, &order.pot) {
        (OrderStatus::Pending, _) => ("pending", None, None, None),
        (OrderStatus::Accepted, Some(pot)) => ("accepted", Some(pot.x), Some(pot.z), Some(pot.yaw)),
        (OrderStatus::Accepted, None) => ("accepted", None, None, None),
        (OrderStatus::Completed, _) => ("completed", None, None, None),
    }
}

fn validate_input(input: &CreateSlotInput) -> Result<()> {
    validate_camera(&input.camera)?;
    for tree in &input.trees {
        validate_tree_numbers(tree.x, tree.z, tree.yaw)?;
    }
    if !(0..=MAX_REPUTATION).contains(&input.reputation) {
        return Err(SaveStoreError::InvalidStructure);
    }
    validate_identifiers(&input.completed_tutorial_milestones)?;
    validate_identifiers(&input.acquired_tool_ids)?;
    let mut order_ids = std::collections::HashSet::new();
    for order in &input.orders {
        validate_identifier(&order.order_id)?;
        if !order_ids.insert(&order.order_id) {
            return Err(SaveStoreError::InvalidStructure);
        }
        match (&order.state, &order.pot) {
            (OrderStatus::Pending | OrderStatus::Completed, None) => {}
            (OrderStatus::Accepted, Some(pot)) => validate_pot(pot)?,
            _ => return Err(SaveStoreError::InvalidStructure),
        }
    }
    Ok(())
}

fn validate_identifier(identifier: &str) -> Result<()> {
    if identifier.trim().is_empty() {
        Err(SaveStoreError::BlankIdentifier)
    } else {
        Ok(())
    }
}

fn validate_identifiers(identifiers: &[String]) -> Result<()> {
    let mut seen = std::collections::HashSet::new();
    for identifier in identifiers {
        validate_identifier(identifier)?;
        if !seen.insert(identifier) {
            return Err(SaveStoreError::InvalidStructure);
        }
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

fn validate_pot(pot: &PotPlacementRecord) -> Result<()> {
    if [pot.x, pot.z, pot.yaw].into_iter().all(f64::is_finite) {
        Ok(())
    } else {
        Err(SaveStoreError::NonFinitePotPlacement)
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
    validate_exact_tables(connection)?;
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
    validate_required_columns(
        connection,
        "progress",
        vec![
            column("singleton", "INTEGER", false, 1),
            column("reputation", "INTEGER", true, 0),
            column("tutorials_enabled", "BOOLEAN", true, 0),
        ],
    )?;
    validate_required_columns(
        connection,
        "tutorial_milestones",
        vec![column("milestone_id", "TEXT", false, 1)],
    )?;
    validate_required_columns(
        connection,
        "acquired_tools",
        vec![column("tool_id", "TEXT", false, 1)],
    )?;
    validate_required_columns(
        connection,
        "orders",
        vec![
            column("order_id", "TEXT", false, 1),
            column("state", "TEXT", true, 0),
            column("pot_x", "REAL", false, 0),
            column("pot_z", "REAL", false, 0),
            column("pot_yaw", "REAL", false, 0),
        ],
    )?;
    if !has_auto_generated_diagram_key(connection)? {
        return Err(rusqlite::Error::InvalidQuery);
    }

    if !has_unique_key(connection, "metadata", &["slot_id"], false)?
        || !has_unique_key(connection, "diagrams", &["diagram_json"], true)?
    {
        return Err(rusqlite::Error::InvalidQuery);
    }
    validate_required_check_constraints(connection)?;
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

fn validate_required_check_constraints(connection: &Connection) -> rusqlite::Result<()> {
    let progress_sql: String = connection.query_row(
        "SELECT sql FROM sqlite_schema WHERE type = 'table' AND name = 'progress'",
        [],
        |row| row.get(0),
    )?;
    let orders_sql: String = connection.query_row(
        "SELECT sql FROM sqlite_schema WHERE type = 'table' AND name = 'orders'",
        [],
        |row| row.get(0),
    )?;
    let probe = Connection::open_in_memory()?;
    probe.execute_batch(&progress_sql)?;
    probe.execute("INSERT INTO progress VALUES(1, 0, 1)", [])?;
    probe.execute("DELETE FROM progress", [])?;
    if !is_constraint_error(probe.execute("INSERT INTO progress VALUES(2, 0, 1)", []))
        || !is_constraint_error(probe.execute("INSERT INTO progress VALUES(1, -1, 1)", []))
        || !is_constraint_error(probe.execute("INSERT INTO progress VALUES(1, 0, 2)", []))
        || !is_constraint_error(probe.execute("INSERT INTO progress VALUES(1, 0, NULL)", []))
    {
        return Err(rusqlite::Error::InvalidQuery);
    }

    probe.execute_batch(&orders_sql)?;
    for state in ["pending", "accepted", "completed"] {
        for present_mask in 0_u8..8 {
            let value = |bit| if present_mask & bit == 0 { "NULL" } else { "1" };
            let insert = format!(
                "INSERT INTO orders VALUES('probe-{state}-{present_mask}', '{state}', {}, {}, {})",
                value(1),
                value(2),
                value(4),
            );
            let legal = (state == "accepted" && present_mask == 7)
                || (state != "accepted" && present_mask == 0);
            let result = probe.execute(&insert, []);
            if legal {
                result?;
            } else if !is_constraint_error(result) {
                return Err(rusqlite::Error::InvalidQuery);
            }
        }
    }
    if !is_constraint_error(probe.execute(
        "INSERT INTO orders VALUES('bad-state', 'lost', NULL, NULL, NULL)",
        [],
    )) {
        return Err(rusqlite::Error::InvalidQuery);
    }
    Ok(())
}

fn is_constraint_error(result: rusqlite::Result<usize>) -> bool {
    matches!(
        result,
        Err(rusqlite::Error::SqliteFailure(error, _))
            if error.code == ErrorCode::ConstraintViolation
    )
}

fn has_auto_generated_diagram_key(connection: &Connection) -> rusqlite::Result<bool> {
    let mut statement = connection.prepare("PRAGMA index_list('diagrams')")?;
    let primary_key_index = statement
        .query_map([], |row| row.get::<_, String>(3))?
        .collect::<rusqlite::Result<Vec<_>>>()?
        .into_iter()
        .any(|origin| origin == "pk");
    Ok(!primary_key_index)
}

fn validate_required_columns(
    connection: &Connection,
    table: &str,
    expected: Vec<Column>,
) -> rusqlite::Result<()> {
    let mut statement = connection.prepare(&format!("PRAGMA table_xinfo('{table}')"))?;
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
    if actual.len() != expected.len() {
        return Err(rusqlite::Error::InvalidQuery);
    }
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

fn validate_exact_tables(connection: &Connection) -> rusqlite::Result<()> {
    let mut statement = connection.prepare(
        "SELECT name FROM sqlite_schema
         WHERE type = 'table' AND name NOT LIKE 'sqlite_%'
         ORDER BY name",
    )?;
    let tables = statement
        .query_map([], |row| row.get::<_, String>(0))?
        .collect::<rusqlite::Result<Vec<_>>>()?;
    let expected = vec![
        "acquired_tools",
        "camera",
        "diagrams",
        "metadata",
        "orders",
        "progress",
        "trees",
        "tutorial_milestones",
    ];
    if tables == expected {
        Ok(())
    } else {
        Err(rusqlite::Error::InvalidQuery)
    }
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
             AND tbl_name IN (
               'metadata', 'camera', 'diagrams', 'trees', 'progress', 'tutorial_milestones',
               'acquired_tools', 'orders'
             )
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
            reputation: 0,
            tutorials_enabled: true,
            completed_tutorial_milestones: vec![],
            acquired_tool_ids: vec!["sprout-spawner".into()],
            orders: vec![OrderRecord {
                order_id: "starter-double-cut".into(),
                state: OrderStatus::Pending,
                pot: None,
            }],
        }
    }

    // This catches omitted tutorial/tool persistence and non-idempotent progression retries.
    #[test]
    fn persists_tutorial_and_tool_progression_idempotently() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot_id = store.create(basic_input()).unwrap().slot_id;

        let created = store.load(&slot_id).unwrap();
        assert!(created.tutorials_enabled);
        assert_eq!(created.completed_tutorial_milestones, Vec::<String>::new());
        assert_eq!(created.acquired_tool_ids, vec!["sprout-spawner"]);

        store.set_tutorials_enabled(&slot_id, false).unwrap();
        store
            .complete_tutorial_milestone(&slot_id, "welcome")
            .unwrap();
        store
            .complete_tutorial_milestone(&slot_id, "welcome")
            .unwrap();
        store.acquire_tool(&slot_id, "double-cut-tool").unwrap();
        store.acquire_tool(&slot_id, "double-cut-tool").unwrap();

        let loaded = store.load(&slot_id).unwrap();
        assert!(!loaded.tutorials_enabled);
        assert_eq!(loaded.completed_tutorial_milestones, vec!["welcome"]);
        assert_eq!(
            loaded.acquired_tool_ids,
            vec!["double-cut-tool", "sprout-spawner"]
        );
    }

    // This catches catalog reconciliation that resets preserved state or retains obsolete pots.
    #[test]
    fn replaces_order_ids_preserving_matching_state_and_removing_absent_pots() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let mut input = basic_input();
        input.orders = vec![
            OrderRecord {
                order_id: "a".into(),
                state: OrderStatus::Pending,
                pot: None,
            },
            OrderRecord {
                order_id: "removed".into(),
                state: OrderStatus::Pending,
                pot: None,
            },
        ];
        let slot_id = store.create(input).unwrap().slot_id;
        let kept_pot = PotPlacementRecord {
            x: 3.0,
            z: -6.0,
            yaw: 0.5,
        };
        store.accept_order(&slot_id, "a", kept_pot.clone()).unwrap();
        store
            .accept_order(
                &slot_id,
                "removed",
                PotPlacementRecord {
                    x: 4.0,
                    z: -8.0,
                    yaw: 0.75,
                },
            )
            .unwrap();

        store
            .replace_order_ids(&slot_id, &["a".into(), "b".into()])
            .unwrap();

        assert_eq!(
            store.load(&slot_id).unwrap().orders,
            vec![
                OrderRecord {
                    order_id: "a".into(),
                    state: OrderStatus::Accepted,
                    pot: Some(kept_pot),
                },
                OrderRecord {
                    order_id: "b".into(),
                    state: OrderStatus::Pending,
                    pot: None,
                },
            ]
        );
    }

    // This catches structural validation that ignores unauthorised schema additions.
    #[test]
    fn rejects_unknown_columns_and_tables() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());

        for (slot_id, mutation) in [
            (
                "unknown-column",
                "ALTER TABLE progress ADD COLUMN legacy INTEGER",
            ),
            ("unknown-table", "CREATE TABLE legacy (value TEXT)"),
        ] {
            let path = temp.path().join(format!("{slot_id}.sqlite3"));
            store.create_at(&path, slot_id, 0, basic_input()).unwrap();
            Connection::open(path)
                .unwrap()
                .execute_batch(mutation)
                .unwrap();

            assert!(matches!(
                store.load(slot_id),
                Err(SaveStoreError::InvalidStructure)
            ));
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

    // This catches partial persistence, duplicate rewards, and retry paths that mutate twice.
    #[test]
    fn inserts_updates_and_completes_an_order_atomically_with_idempotent_retries() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot_id = store.create(basic_input()).unwrap().slot_id;

        let inserted = store
            .insert_tree(&slot_id, tree("tree-2", "diagram-b"))
            .unwrap();
        assert!(inserted > 0);
        store
            .update_tree(&slot_id, tree("tree-2", "diagram-c"))
            .unwrap();

        let first_pot = PotPlacementRecord {
            x: 3.0,
            z: -6.0,
            yaw: 0.5,
        };
        store
            .accept_order(&slot_id, "starter-double-cut", first_pot.clone())
            .unwrap();
        let accepted = store.load(&slot_id).unwrap();
        store
            .accept_order(&slot_id, "starter-double-cut", first_pot)
            .unwrap();
        assert_eq!(store.load(&slot_id).unwrap(), accepted);

        store.abandon_order(&slot_id, "starter-double-cut").unwrap();
        let abandoned = store.load(&slot_id).unwrap();
        store.abandon_order(&slot_id, "starter-double-cut").unwrap();
        assert_eq!(store.load(&slot_id).unwrap(), abandoned);

        store
            .accept_order(
                &slot_id,
                "starter-double-cut",
                PotPlacementRecord {
                    x: 4.0,
                    z: -8.0,
                    yaw: 0.75,
                },
            )
            .unwrap();
        assert_eq!(
            store
                .complete_order(&slot_id, "starter-double-cut", 1)
                .unwrap(),
            1
        );
        let completed = store.load(&slot_id).unwrap();
        assert_eq!(
            store
                .complete_order(&slot_id, "starter-double-cut", 1)
                .unwrap(),
            1
        );
        assert_eq!(store.load(&slot_id).unwrap(), completed);
        assert_eq!(completed.reputation, 1);
        assert_eq!(
            completed.orders,
            vec![OrderRecord {
                order_id: "starter-double-cut".into(),
                state: OrderStatus::Completed,
                pot: None,
            }]
        );
        assert!(completed.trees.iter().any(|tree| tree.tree_id == "tree-2"));
    }

    // This catches retry handling that accepts a conflicting tree payload or advances metadata.
    #[test]
    fn tree_insertion_retries_only_byte_identical_payloads() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot_id = store.create(basic_input()).unwrap().slot_id;
        let mut inserted_tree = tree("tree-2", "diagram-b");
        inserted_tree.x = 4.0;
        inserted_tree.z = -8.0;
        inserted_tree.yaw = 0.75;

        let diagram_key = store.insert_tree(&slot_id, inserted_tree.clone()).unwrap();
        let after_insert = store.load(&slot_id).unwrap();
        assert_eq!(
            store.insert_tree(&slot_id, inserted_tree.clone()).unwrap(),
            diagram_key
        );
        assert_eq!(store.load(&slot_id).unwrap(), after_insert);

        let mut conflicting_diagram = inserted_tree.clone();
        conflicting_diagram.diagram_json = "diagram-c".into();
        assert!(store.insert_tree(&slot_id, conflicting_diagram).is_err());
        let mut conflicting_placement = inserted_tree;
        conflicting_placement.x = 5.0;
        assert!(store.insert_tree(&slot_id, conflicting_placement).is_err());
        assert_eq!(store.load(&slot_id).unwrap(), after_insert);
    }

    // This catches lifecycle guards that silently accept incompatible states or payloads.
    #[test]
    fn order_operations_reject_conflicts_without_mutating_the_slot() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot_id = store.create(basic_input()).unwrap().slot_id;
        let initial = store.load(&slot_id).unwrap();

        assert!(store
            .complete_order(&slot_id, "starter-double-cut", 1)
            .is_err());
        assert!(store
            .accept_order(
                &slot_id,
                "missing",
                PotPlacementRecord {
                    x: 1.0,
                    z: 2.0,
                    yaw: 3.0,
                },
            )
            .is_err());
        assert_eq!(store.load(&slot_id).unwrap(), initial);

        let accepted_pot = PotPlacementRecord {
            x: 3.0,
            z: -6.0,
            yaw: 0.5,
        };
        store
            .accept_order(&slot_id, "starter-double-cut", accepted_pot)
            .unwrap();
        let accepted = store.load(&slot_id).unwrap();
        assert!(store
            .accept_order(
                &slot_id,
                "starter-double-cut",
                PotPlacementRecord {
                    x: 4.0,
                    z: -6.0,
                    yaw: 0.5,
                },
            )
            .is_err());
        assert_eq!(store.load(&slot_id).unwrap(), accepted);

        store
            .complete_order(&slot_id, "starter-double-cut", 2)
            .unwrap();
        let completed = store.load(&slot_id).unwrap();
        assert!(store.abandon_order(&slot_id, "starter-double-cut").is_err());
        assert!(store
            .accept_order(
                &slot_id,
                "starter-double-cut",
                PotPlacementRecord {
                    x: 3.0,
                    z: -6.0,
                    yaw: 0.5,
                },
            )
            .is_err());
        assert_eq!(store.load(&slot_id).unwrap(), completed);
    }

    // This catches unchecked numeric inputs and verifies validation happens before mutation.
    #[test]
    fn order_operations_reject_negative_rewards_and_non_finite_pots() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot_id = store.create(basic_input()).unwrap().slot_id;
        let initial = store.load(&slot_id).unwrap();

        assert!(store
            .accept_order(
                &slot_id,
                "starter-double-cut",
                PotPlacementRecord {
                    x: f64::INFINITY,
                    z: 0.0,
                    yaw: 0.0,
                },
            )
            .is_err());
        assert!(store
            .complete_order(&slot_id, "starter-double-cut", -1)
            .is_err());
        assert_eq!(store.load(&slot_id).unwrap(), initial);
    }

    // This catches a failed final metadata write leaving order state or reputation committed.
    #[test]
    fn completion_rolls_back_state_and_reputation_when_the_transaction_fails() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot_id = store.create(basic_input()).unwrap().slot_id;
        store
            .accept_order(
                &slot_id,
                "starter-double-cut",
                PotPlacementRecord {
                    x: 3.0,
                    z: -6.0,
                    yaw: 0.5,
                },
            )
            .unwrap();
        let path = temp.path().join(format!("{slot_id}.sqlite3"));
        Connection::open(path)
            .unwrap()
            .execute(
                "UPDATE metadata SET updated_at_ms = ?1 WHERE singleton = 1",
                [i64::MAX],
            )
            .unwrap();
        let before = store.load(&slot_id).unwrap();

        assert!(matches!(
            store.complete_order(&slot_id, "starter-double-cut", 1),
            Err(SaveStoreError::TimestampOverflow)
        ));
        assert_eq!(store.load(&slot_id).unwrap(), before);
    }

    // This catches reputation bounds that use Rust's integer range instead of the JSON safe range.
    #[test]
    fn completion_rejects_javascript_unsafe_reputation_and_rolls_back_the_order() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot_id = store.create(basic_input()).unwrap().slot_id;
        store
            .accept_order(
                &slot_id,
                "starter-double-cut",
                PotPlacementRecord {
                    x: 3.0,
                    z: -6.0,
                    yaw: 0.5,
                },
            )
            .unwrap();
        let path = temp.path().join(format!("{slot_id}.sqlite3"));
        Connection::open(path)
            .unwrap()
            .execute(
                "UPDATE progress SET reputation = ?1 WHERE singleton = 1",
                [9_007_199_254_740_991_i64],
            )
            .unwrap();
        let before = store.load(&slot_id).unwrap();

        assert!(matches!(
            store.complete_order(&slot_id, "starter-double-cut", 1),
            Err(SaveStoreError::ReputationOverflow)
        ));
        assert_eq!(store.load(&slot_id).unwrap(), before);
    }

    // This catches i64::MAX reaching the wire through an existing save or an idempotent completion.
    #[test]
    fn rejects_direct_i64_max_reputation_on_load() {
        let temp = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temp.path().to_path_buf());
        let slot_id = store.create(basic_input()).unwrap().slot_id;
        let path = temp.path().join(format!("{slot_id}.sqlite3"));
        Connection::open(path)
            .unwrap()
            .execute(
                "UPDATE progress SET reputation = ?1 WHERE singleton = 1",
                [i64::MAX],
            )
            .unwrap();

        assert!(matches!(
            store.load(&slot_id),
            Err(SaveStoreError::InvalidStructure)
        ));
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
                 CREATE TABLE progress(singleton INTEGER PRIMARY KEY CHECK(singleton = 1),reputation INTEGER NOT NULL CHECK(reputation >= 0),tutorials_enabled BOOLEAN NOT NULL CHECK(tutorials_enabled IN (0, 1)));
                 CREATE TABLE tutorial_milestones(milestone_id TEXT PRIMARY KEY);
                 CREATE TABLE acquired_tools(tool_id TEXT PRIMARY KEY);
                 CREATE TABLE orders(order_id TEXT PRIMARY KEY,state TEXT NOT NULL CHECK(state IN ('pending','accepted','completed')),
                    pot_x REAL,pot_z REAL,pot_yaw REAL,
                    CHECK((state = 'accepted' AND pot_x IS NOT NULL AND pot_z IS NOT NULL AND pot_yaw IS NOT NULL)
                       OR (state IN ('pending','completed') AND pot_x IS NULL AND pot_z IS NULL AND pot_yaw IS NULL)));
                 CREATE VIEW tree_names AS SELECT tree_id FROM trees;
                 INSERT INTO metadata VALUES(1, 'equivalent', 'Equivalent', 12);
                 INSERT INTO camera VALUES(1, 1, 2, 3, .25, -.5);
                 INSERT INTO diagrams VALUES(7, '{\"regions\":[],\"nodes\":[],\"wires\":[]}');
                 INSERT INTO trees VALUES('tree-a', 7, 4, 5, .75);
                 INSERT INTO progress VALUES(1, 0, 1);
                 INSERT INTO orders VALUES('starter-double-cut', 'pending', NULL, NULL, NULL);",
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
    fn rejects_a_diagram_key_without_sqlite_rowid_alias_behavior() {
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
                 INSERT INTO trees VALUES('tree-a', 7, 4, 5, .75);
                 INSERT INTO progress VALUES(1, 0, 1);
                 INSERT INTO orders VALUES('starter-double-cut', 'pending', NULL, NULL, NULL);",
            )
            .unwrap();

        assert!(matches!(
            SaveStore::new(temp.path().to_path_buf()).load("affinity"),
            Err(SaveStoreError::InvalidStructure)
        ));
    }

    #[test]
    fn updates_an_affinity_equivalent_schema_with_an_auto_generated_diagram_key() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("affinity.sqlite3");
        let connection = Connection::open(&path).unwrap();
        connection
            .execute_batch(
                &SCHEMA
                    .replace("INTEGER", "int")
                    .replace("TEXT", "varchar(256)")
                    .replace("REAL", "double precision")
                    .replace(
                        "diagram_key int PRIMARY KEY",
                        "diagram_key INTEGER PRIMARY KEY",
                    ),
            )
            .unwrap();
        connection
            .execute_batch(
                "INSERT INTO metadata VALUES(1, 'affinity', 'Affinity', 12);
                 INSERT INTO camera VALUES(1, 1, 2, 3, .25, -.5);
                 INSERT INTO diagrams VALUES(7, '{\"regions\":[],\"nodes\":[],\"wires\":[]}');
                 INSERT INTO trees VALUES('tree-a', 7, 4, 5, .75);
                 INSERT INTO progress VALUES(1, 0, 1);
                 INSERT INTO orders VALUES('starter-double-cut', 'pending', NULL, NULL, NULL);",
            )
            .unwrap();

        let store = SaveStore::new(temp.path().to_path_buf());
        let changed_key = store
            .update_tree(
                "affinity",
                TreeUpdate {
                    tree_id: "tree-a".into(),
                    diagram_json: DOUBLE_CUT.into(),
                    x: 8.0,
                    z: 9.0,
                    yaw: 1.0,
                },
            )
            .unwrap();
        let loaded = store.load("affinity").unwrap();

        assert_eq!(loaded.slot_id, "affinity");
        assert_eq!(
            loaded.trees,
            vec![TreeRecord {
                tree_id: "tree-a".into(),
                diagram_key: changed_key,
                x: 8.0,
                z: 9.0,
                yaw: 1.0,
            }]
        );
        assert_eq!(
            loaded
                .diagrams
                .iter()
                .find(|diagram| diagram.diagram_key == changed_key),
            Some(&DiagramRecord {
                diagram_key: changed_key,
                diagram_json: DOUBLE_CUT.into(),
            })
        );
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

    // This catches treating the required columns as a subset instead of the complete current shape.
    #[test]
    fn rejects_extra_columns_in_required_tables() {
        let temp = tempfile::tempdir().unwrap();
        for (slot_id, extra_column) in [
            ("extra-metadata-column", "legacy_version INTEGER"),
            (
                "extra-generated-column",
                "legacy_version INTEGER GENERATED ALWAYS AS (0) VIRTUAL",
            ),
        ] {
            let path = temp.path().join(format!("{slot_id}.sqlite3"));
            let connection = Connection::open(path).unwrap();
            connection
                .execute_batch(&SCHEMA.replace(
                    "updated_at_ms INTEGER NOT NULL",
                    &format!("updated_at_ms INTEGER NOT NULL, {extra_column}"),
                ))
                .unwrap();
            connection
                .execute_batch(&format!(
                    "INSERT INTO metadata(singleton, slot_id, display_name, updated_at_ms)
                     VALUES(1, '{slot_id}', 'Invalid', 0);
                     INSERT INTO camera VALUES(1, 0, 0, 0, 0, 0);
                     INSERT INTO progress VALUES(1, 0, 1);
                     INSERT INTO orders VALUES('starter-double-cut', 'pending', NULL, NULL, NULL);"
                ))
                .unwrap();

            assert!(
                matches!(
                    SaveStore::new(temp.path().to_path_buf()).load(slot_id),
                    Err(SaveStoreError::InvalidStructure)
                ),
                "{slot_id}"
            );
        }
    }

    // This catches accepting lookalike progress/order tables that do not enforce the save model.
    #[test]
    fn rejects_missing_progress_and_order_schema_semantics() {
        let temp = tempfile::tempdir().unwrap();
        let cases = [
            (
                "missing-progress-check",
                SCHEMA.replace("CHECK (reputation >= 0)", ""),
            ),
            (
                "missing-order-payload-check",
                SCHEMA.replace(
                    "CHECK (\n    (state = 'accepted' AND pot_x IS NOT NULL AND pot_z IS NOT NULL AND pot_yaw IS NOT NULL)\n    OR\n    (state IN ('pending', 'completed') AND pot_x IS NULL AND pot_z IS NULL AND pot_yaw IS NULL)\n  )",
                    "CHECK (1)",
                ),
            ),
            (
                "non-unique-order-id",
                SCHEMA.replace("order_id TEXT PRIMARY KEY", "order_id TEXT"),
            ),
        ];

        for (slot_id, schema) in cases {
            let path = temp.path().join(format!("{slot_id}.sqlite3"));
            let connection = Connection::open(path).unwrap();
            connection.execute_batch(&schema).unwrap();
            connection
                .execute_batch(&format!(
                    "INSERT INTO metadata VALUES(1, '{slot_id}', 'Invalid', 0);
                     INSERT INTO camera VALUES(1, 0, 0, 0, 0, 0);
                     INSERT INTO progress VALUES(1, 0, 1);
                     INSERT INTO orders VALUES('starter-double-cut', 'pending', NULL, NULL, NULL);"
                ))
                .unwrap();
            assert!(
                matches!(
                    SaveStore::new(temp.path().to_path_buf()).load(slot_id),
                    Err(SaveStoreError::InvalidStructure)
                ),
                "{slot_id}"
            );
        }
    }

    // This catches constraints that inspect only one pot coordinate and permit partial rows.
    #[test]
    fn rejects_order_schemas_that_permit_partial_pots() {
        let temp = tempfile::tempdir().unwrap();
        let required_payload_check = "CHECK (\n    (state = 'accepted' AND pot_x IS NOT NULL AND pot_z IS NOT NULL AND pot_yaw IS NOT NULL)\n    OR\n    (state IN ('pending', 'completed') AND pot_x IS NULL AND pot_z IS NULL AND pot_yaw IS NULL)\n  )";

        for coordinate in ["pot_x", "pot_z", "pot_yaw"] {
            let slot_id = format!("partial-{}", coordinate.replace('_', "-"));
            let weaker_check = format!(
                "CHECK ((state = 'accepted' AND {coordinate} IS NOT NULL) OR
                 (state IN ('pending', 'completed') AND {coordinate} IS NULL))"
            );
            let schema = SCHEMA.replace(required_payload_check, &weaker_check);
            let path = temp.path().join(format!("{slot_id}.sqlite3"));
            let connection = Connection::open(path).unwrap();
            connection.execute_batch(&schema).unwrap();
            connection
                .execute_batch(&format!(
                    "INSERT INTO metadata VALUES(1, '{slot_id}', 'Invalid', 0);
                     INSERT INTO camera VALUES(1, 0, 0, 0, 0, 0);
                     INSERT INTO progress VALUES(1, 0, 1);
                     INSERT INTO orders VALUES('starter-double-cut', 'pending', NULL, NULL, NULL);"
                ))
                .unwrap();

            assert!(
                matches!(
                    SaveStore::new(temp.path().to_path_buf()).load(&slot_id),
                    Err(SaveStoreError::InvalidStructure)
                ),
                "{coordinate}"
            );
        }
    }

    // This catches load paths that trust rows merely because their table DDL is valid.
    #[test]
    fn load_rejects_invalid_progress_and_order_rows() {
        let temp = tempfile::tempdir().unwrap();
        let cases = [
            (
                "missing-progress-row",
                "DELETE FROM progress WHERE singleton = 1",
            ),
            (
                "negative-reputation",
                "PRAGMA ignore_check_constraints = ON; UPDATE progress SET reputation = -1",
            ),
            (
                "unknown-order-state",
                "PRAGMA ignore_check_constraints = ON; UPDATE orders SET state = 'lost'",
            ),
            (
                "pending-order-pot",
                "PRAGMA ignore_check_constraints = ON; UPDATE orders SET pot_x = 1, pot_z = 2, pot_yaw = 3",
            ),
            (
                "accepted-order-missing-pot",
                "PRAGMA ignore_check_constraints = ON; UPDATE orders SET state = 'accepted'",
            ),
            (
                "accepted-order-non-finite-pot",
                "PRAGMA ignore_check_constraints = ON; UPDATE orders SET state = 'accepted', pot_x = 1e999, pot_z = 2, pot_yaw = 3",
            ),
        ];

        for (slot_id, mutation) in cases {
            let store = SaveStore::new(temp.path().to_path_buf());
            let path = temp.path().join(format!("{slot_id}.sqlite3"));
            store.create_at(&path, slot_id, 0, basic_input()).unwrap();
            Connection::open(path)
                .unwrap()
                .execute_batch(mutation)
                .unwrap();
            assert!(matches!(
                store.load(slot_id),
                Err(SaveStoreError::InvalidStructure)
            ));
        }
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
             INSERT INTO progress VALUES(1, 0, 1);
             INSERT INTO orders VALUES('starter-double-cut', 'pending', NULL, NULL, NULL);
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
             INSERT INTO progress VALUES(1, 0, 1);
             INSERT INTO orders VALUES('starter-double-cut', 'pending', NULL, NULL, NULL);
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
                reputation: 0,
                tutorials_enabled: true,
                completed_tutorial_milestones: vec![],
                acquired_tool_ids: vec![],
                orders: vec![],
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
                reputation: 0,
                tutorials_enabled: true,
                completed_tutorial_milestones: vec![],
                acquired_tool_ids: vec![],
                orders: vec![],
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
