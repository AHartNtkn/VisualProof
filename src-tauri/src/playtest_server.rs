use crate::save_store::{
    AuthoredContentStore, CameraRecord, CreateSlotInput, OrderContentRecord, OrderContentStore,
    PotPlacementRecord, SaveStore, SaveStoreError, ToolContentRecord, TreeUpdate,
    TutorialContentRecord,
};
use axum::{
    extract::{Request, State},
    http::{header, HeaderValue, Method, StatusCode},
    middleware::{self, Next},
    response::{IntoResponse, Response},
    routing::{get, post},
    Json, Router,
};
use serde::Deserialize;
use tower_http::cors::CorsLayer;

const TOKEN_HEADER: &str = "x-orchard-playtest-token";

#[derive(Clone)]
pub struct PlaytestServerConfig {
    pub token: String,
    pub allowed_origin: HeaderValue,
}

#[derive(Clone)]
struct AppState {
    store: SaveStore,
    order_content: OrderContentStore,
    authored_content: AuthoredContentStore,
    config: PlaytestServerConfig,
}

pub fn router(store: SaveStore, config: PlaytestServerConfig) -> Router {
    router_with_content_stores(
        store,
        OrderContentStore::production(),
        AuthoredContentStore::production(),
        config,
    )
}

pub fn router_with_content_stores(
    store: SaveStore,
    order_content: OrderContentStore,
    authored_content: AuthoredContentStore,
    config: PlaytestServerConfig,
) -> Router {
    let state = AppState {
        store,
        order_content,
        authored_content,
        config,
    };
    let cors = CorsLayer::new()
        .allow_origin(state.config.allowed_origin.clone())
        .allow_methods([Method::GET, Method::POST])
        .allow_headers([
            header::CONTENT_TYPE,
            header::HeaderName::from_static(TOKEN_HEADER),
        ]);

    Router::new()
        .route("/__orchard_playtest/health", get(health))
        .route("/__orchard_playtest/save/list", post(list))
        .route("/__orchard_playtest/save/create", post(create))
        .route("/__orchard_playtest/save/load", post(load))
        .route("/__orchard_playtest/save/insert-tree", post(insert_tree))
        .route("/__orchard_playtest/save/update-tree", post(update_tree))
        .route(
            "/__orchard_playtest/save/update-camera",
            post(update_camera),
        )
        .route("/__orchard_playtest/save/accept-order", post(accept_order))
        .route(
            "/__orchard_playtest/save/abandon-order",
            post(abandon_order),
        )
        .route(
            "/__orchard_playtest/save/complete-order",
            post(complete_order),
        )
        .route(
            "/__orchard_playtest/save/set-tutorials-enabled",
            post(set_tutorials_enabled),
        )
        .route(
            "/__orchard_playtest/save/complete-tutorial-milestone",
            post(complete_tutorial_milestone),
        )
        .route("/__orchard_playtest/save/acquire-tool", post(acquire_tool))
        .route(
            "/__orchard_playtest/content/orders",
            post(save_order_catalog),
        )
        .route(
            "/__orchard_playtest/content/tutorial",
            post(save_tutorial_content),
        )
        .route("/__orchard_playtest/content/tools", post(save_tool_content))
        .with_state(state.clone())
        .layer(cors)
        .layer(middleware::from_fn_with_state(state, authenticate))
}

async fn authenticate(State(state): State<AppState>, request: Request, next: Next) -> Response {
    if request.headers().get(header::ORIGIN) != Some(&state.config.allowed_origin) {
        return StatusCode::FORBIDDEN.into_response();
    }
    if request.method() == Method::OPTIONS
        && request
            .headers()
            .contains_key(header::ACCESS_CONTROL_REQUEST_METHOD)
    {
        return next.run(request).await;
    }
    let supplied_token = request
        .headers()
        .get(TOKEN_HEADER)
        .and_then(|value| value.to_str().ok());
    if supplied_token != Some(state.config.token.as_str()) {
        return StatusCode::UNAUTHORIZED.into_response();
    }
    next.run(request).await
}

async fn health() -> StatusCode {
    StatusCode::NO_CONTENT
}

async fn list(
    State(state): State<AppState>,
    Json(_): Json<serde_json::Value>,
) -> Result<Json<Vec<crate::save_store::SlotListEntry>>, StoreError> {
    state.store.list().map(Json).map_err(StoreError)
}

async fn create(
    State(state): State<AppState>,
    Json(input): Json<CreateSlotInput>,
) -> Result<Json<crate::save_store::SlotListEntry>, StoreError> {
    state.store.create(input).map(Json).map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SlotRequest {
    slot_id: String,
}

async fn load(
    State(state): State<AppState>,
    Json(input): Json<SlotRequest>,
) -> Result<Json<crate::save_store::LoadedSlot>, StoreError> {
    state
        .store
        .load(&input.slot_id)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct UpdateTreeRequest {
    slot_id: String,
    update: TreeUpdate,
}

async fn insert_tree(
    State(state): State<AppState>,
    Json(input): Json<UpdateTreeRequest>,
) -> Result<Json<i64>, StoreError> {
    state
        .store
        .insert_tree(&input.slot_id, input.update)
        .map(Json)
        .map_err(StoreError)
}

async fn update_tree(
    State(state): State<AppState>,
    Json(input): Json<UpdateTreeRequest>,
) -> Result<Json<i64>, StoreError> {
    state
        .store
        .update_tree(&input.slot_id, input.update)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct UpdateCameraRequest {
    slot_id: String,
    camera: CameraRecord,
}

async fn update_camera(
    State(state): State<AppState>,
    Json(input): Json<UpdateCameraRequest>,
) -> Result<Json<()>, StoreError> {
    state
        .store
        .update_camera(&input.slot_id, input.camera)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct AcceptOrderRequest {
    slot_id: String,
    order_id: String,
    pot: PotPlacementRecord,
}

async fn accept_order(
    State(state): State<AppState>,
    Json(input): Json<AcceptOrderRequest>,
) -> Result<Json<()>, StoreError> {
    state
        .store
        .accept_order(&input.slot_id, &input.order_id, input.pot)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct OrderRequest {
    slot_id: String,
    order_id: String,
}

async fn abandon_order(
    State(state): State<AppState>,
    Json(input): Json<OrderRequest>,
) -> Result<Json<()>, StoreError> {
    state
        .store
        .abandon_order(&input.slot_id, &input.order_id)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct CompleteOrderRequest {
    slot_id: String,
    order_id: String,
    reward: i64,
}

async fn complete_order(
    State(state): State<AppState>,
    Json(input): Json<CompleteOrderRequest>,
) -> Result<Json<i64>, StoreError> {
    state
        .store
        .complete_order(&input.slot_id, &input.order_id, input.reward)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SetTutorialsEnabledRequest {
    slot_id: String,
    enabled: bool,
}

async fn set_tutorials_enabled(
    State(state): State<AppState>,
    Json(input): Json<SetTutorialsEnabledRequest>,
) -> Result<Json<()>, StoreError> {
    state
        .store
        .set_tutorials_enabled(&input.slot_id, input.enabled)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct CompleteTutorialMilestoneRequest {
    slot_id: String,
    milestone_id: String,
}

async fn complete_tutorial_milestone(
    State(state): State<AppState>,
    Json(input): Json<CompleteTutorialMilestoneRequest>,
) -> Result<Json<()>, StoreError> {
    state
        .store
        .complete_tutorial_milestone(&input.slot_id, &input.milestone_id)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct AcquireToolRequest {
    slot_id: String,
    tool_id: String,
}

async fn acquire_tool(
    State(state): State<AppState>,
    Json(input): Json<AcquireToolRequest>,
) -> Result<Json<()>, StoreError> {
    state
        .store
        .acquire_tool(&input.slot_id, &input.tool_id)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct SaveOrderCatalogRequest {
    slot_id: String,
    content: Vec<OrderContentRecord>,
}

async fn save_order_catalog(
    State(state): State<AppState>,
    Json(input): Json<SaveOrderCatalogRequest>,
) -> Result<Json<()>, StoreError> {
    state
        .order_content
        .save_order_catalog(&state.store, &input.slot_id, input.content)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SaveTutorialContentRequest {
    content: Vec<TutorialContentRecord>,
}

async fn save_tutorial_content(
    State(state): State<AppState>,
    Json(input): Json<SaveTutorialContentRequest>,
) -> Result<Json<()>, StoreError> {
    state
        .authored_content
        .save_tutorial_content(input.content)
        .map(Json)
        .map_err(StoreError)
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SaveToolContentRequest {
    content: Vec<ToolContentRecord>,
}

async fn save_tool_content(
    State(state): State<AppState>,
    Json(input): Json<SaveToolContentRequest>,
) -> Result<Json<()>, StoreError> {
    state
        .authored_content
        .save_tool_content(input.content)
        .map(Json)
        .map_err(StoreError)
}

struct StoreError(SaveStoreError);

impl IntoResponse for StoreError {
    fn into_response(self) -> Response {
        (StatusCode::BAD_REQUEST, self.0.to_string()).into_response()
    }
}

#[cfg(test)]
mod tests {
    use super::{router, router_with_content_stores, PlaytestServerConfig};
    use crate::save_store::{
        AuthoredContentStore, CameraRecord, OrderContentRecord, OrderContentStore, SaveStore,
    };
    use axum::{
        body::{to_bytes, Body},
        http::{header, HeaderValue, Request, StatusCode},
    };
    use serde_json::{json, Value};
    use tower::ServiceExt;

    const TOKEN: &str = "orchard-playtest-token";
    const ORIGIN: &str = "http://127.0.0.1:1420";

    fn config() -> PlaytestServerConfig {
        PlaytestServerConfig {
            token: TOKEN.into(),
            allowed_origin: HeaderValue::from_static(ORIGIN),
        }
    }

    fn request(path: &str, body: Value) -> Request<Body> {
        Request::builder()
            .method("POST")
            .uri(path)
            .header(header::ORIGIN, ORIGIN)
            .header("x-orchard-playtest-token", TOKEN)
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from(body.to_string()))
            .unwrap()
    }

    async fn response_json(response: axum::response::Response) -> Value {
        let (parts, body) = response.into_parts();
        assert_eq!(parts.status, StatusCode::OK);
        serde_json::from_slice(&to_bytes(body, usize::MAX).await.unwrap()).unwrap()
    }

    // This catches a server that returns success without calling the real SaveStore.
    #[tokio::test]
    async fn authenticated_routes_create_list_load_and_update_an_ordinary_slot() {
        let temporary = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temporary.path().to_path_buf());
        let app = router(store.clone(), config());
        let created = response_json(
            app.clone()
                .oneshot(request(
                    "/__orchard_playtest/save/create",
                    json!({
                        "displayName": "Browser Orchard",
                        "camera": {"x": 1.0, "y": 2.0, "z": 3.0, "yaw": 0.25, "pitch": -0.5},
                        "trees": [{
                            "treeId": "tree-1",
                            "diagramJson": "{\"regions\":[],\"nodes\":[],\"wires\":[]}",
                            "x": 4.0,
                            "z": 5.0,
                            "yaw": 0.75
                        }],
                        "reputation": 0,
                        "tutorialsEnabled": true,
                        "completedTutorialMilestones": [],
                        "acquiredToolIds": ["sprout-spawner"],
                        "orders": [{
                            "orderId": "starter-double-cut",
                            "state": "pending",
                            "pot": null
                        }]
                    }),
                ))
                .await
                .unwrap(),
        )
        .await;
        assert_eq!(created["displayName"], "Browser Orchard");
        assert_eq!(created["error"], Value::Null);
        let slot_id = created["slotId"].as_str().unwrap().to_owned();

        let listed = response_json(
            app.clone()
                .oneshot(request("/__orchard_playtest/save/list", json!({})))
                .await
                .unwrap(),
        )
        .await;
        assert_eq!(listed, json!([created.clone()]));

        let loaded = response_json(
            app.clone()
                .oneshot(request(
                    "/__orchard_playtest/save/load",
                    json!({"slotId": slot_id}),
                ))
                .await
                .unwrap(),
        )
        .await;
        assert_eq!(loaded["displayName"], "Browser Orchard");
        assert_eq!(loaded["camera"]["x"], 1.0);
        assert_eq!(loaded["trees"][0]["treeId"], "tree-1");
        assert_eq!(loaded["reputation"], 0);
        assert_eq!(loaded["tutorialsEnabled"], true);
        assert_eq!(loaded["acquiredToolIds"], json!(["sprout-spawner"]));
        assert_eq!(loaded["orders"][0]["state"], "pending");

        let inserted_tree = response_json(
            app.clone()
                .oneshot(request(
                    "/__orchard_playtest/save/insert-tree",
                    json!({
                        "slotId": slot_id,
                        "update": {
                            "treeId": "tree-2",
                            "diagramJson": "{\"regions\":[],\"nodes\":[{\"id\":\"new\"}],\"wires\":[]}",
                            "x": 12.0,
                            "z": -3.0,
                            "yaw": 0.125
                        }
                    }),
                ))
                .await
                .unwrap(),
        )
        .await;
        assert!(inserted_tree.as_i64().unwrap() > 0);

        assert_eq!(
            response_json(
                app.clone()
                    .oneshot(request(
                        "/__orchard_playtest/save/accept-order",
                        json!({
                            "slotId": slot_id,
                            "orderId": "starter-double-cut",
                            "pot": {"x": 3.0, "z": -6.0, "yaw": 0.5}
                        }),
                    ))
                    .await
                    .unwrap(),
            )
            .await,
            Value::Null
        );
        assert_eq!(
            response_json(
                app.clone()
                    .oneshot(request(
                        "/__orchard_playtest/save/abandon-order",
                        json!({"slotId": slot_id, "orderId": "starter-double-cut"}),
                    ))
                    .await
                    .unwrap(),
            )
            .await,
            Value::Null
        );
        assert_eq!(
            response_json(
                app.clone()
                    .oneshot(request(
                        "/__orchard_playtest/save/accept-order",
                        json!({
                            "slotId": slot_id,
                            "orderId": "starter-double-cut",
                            "pot": {"x": 4.0, "z": -8.0, "yaw": 0.75}
                        }),
                    ))
                    .await
                    .unwrap(),
            )
            .await,
            Value::Null
        );
        assert_eq!(
            response_json(
                app.clone()
                    .oneshot(request(
                        "/__orchard_playtest/save/complete-order",
                        json!({"slotId": slot_id, "orderId": "starter-double-cut", "reward": 2}),
                    ))
                    .await
                    .unwrap(),
            )
            .await,
            json!(2)
        );
        assert_eq!(
            response_json(
                app.clone()
                    .oneshot(request(
                        "/__orchard_playtest/save/set-tutorials-enabled",
                        json!({"slotId": slot_id, "enabled": false}),
                    ))
                    .await
                    .unwrap(),
            )
            .await,
            Value::Null
        );
        assert_eq!(
            response_json(
                app.clone()
                    .oneshot(request(
                        "/__orchard_playtest/save/complete-tutorial-milestone",
                        json!({"slotId": slot_id, "milestoneId": "move"}),
                    ))
                    .await
                    .unwrap(),
            )
            .await,
            Value::Null
        );
        assert_eq!(
            response_json(
                app.clone()
                    .oneshot(request(
                        "/__orchard_playtest/save/acquire-tool",
                        json!({"slotId": slot_id, "toolId": "double-cut"}),
                    ))
                    .await
                    .unwrap(),
            )
            .await,
            Value::Null
        );

        let updated_tree = response_json(
            app.clone()
                .oneshot(request(
                    "/__orchard_playtest/save/update-tree",
                    json!({
                        "slotId": slot_id,
                        "update": {
                            "treeId": "tree-1",
                            "diagramJson": "{\"regions\":[{\"id\":\"cut\"}],\"nodes\":[],\"wires\":[]}",
                            "x": 6.0,
                            "z": 7.0,
                            "yaw": 1.25
                        }
                    }),
                ))
                .await
                .unwrap(),
        )
        .await;
        assert!(updated_tree.as_i64().unwrap() > 0);

        let updated_camera = CameraRecord {
            x: 8.0,
            y: 9.0,
            z: 10.0,
            yaw: -0.25,
            pitch: 0.5,
        };
        assert_eq!(
            response_json(
                app.oneshot(request(
                    "/__orchard_playtest/save/update-camera",
                    json!({"slotId": slot_id, "camera": updated_camera}),
                ))
                .await
                .unwrap(),
            )
            .await,
            Value::Null
        );

        let persisted = SaveStore::new(temporary.path().to_path_buf())
            .load(&slot_id)
            .unwrap();
        assert_eq!(persisted.camera, updated_camera);
        assert_eq!(persisted.trees[0].x, 6.0);
        assert_eq!(persisted.trees[0].z, 7.0);
        assert_eq!(persisted.trees[0].yaw, 1.25);
        assert!(persisted.diagrams.iter().any(|diagram| {
            diagram.diagram_json == "{\"regions\":[{\"id\":\"cut\"}],\"nodes\":[],\"wires\":[]}"
        }));
        assert!(persisted.trees.iter().any(|tree| tree.tree_id == "tree-2"));
        assert_eq!(persisted.reputation, 2);
        assert!(!persisted.tutorials_enabled);
        assert_eq!(persisted.completed_tutorial_milestones, vec!["move"]);
        assert_eq!(
            persisted.acquired_tool_ids,
            vec!["double-cut", "sprout-spawner"]
        );
        assert_eq!(
            persisted.orders[0].state,
            crate::save_store::OrderStatus::Completed
        );
        assert_eq!(persisted.orders[0].pot, None);
    }

    // This catches a browser-only content authority, persistence under the wrong order identity,
    // or a route that omits save reconciliation.
    #[tokio::test]
    async fn order_catalog_route_persists_content_and_reconciles_the_same_save_store() {
        let temporary = tempfile::tempdir().unwrap();
        let saves = SaveStore::new(temporary.path().join("saves"));
        let content_path = temporary.path().join("orders.json");
        std::fs::write(&content_path, "[]\n").unwrap();
        let app = router_with_content_stores(
            saves.clone(),
            OrderContentStore::new(content_path.clone()),
            AuthoredContentStore::new(
                temporary.path().join("tutorial.json"),
                temporary.path().join("tools.json"),
            ),
            config(),
        );
        let created = response_json(
            app.clone()
                .oneshot(request(
                    "/__orchard_playtest/save/create",
                    json!({
                        "displayName": "Content Orchard",
                        "camera": {"x": 0.0, "y": 1.7, "z": 8.0, "yaw": 0.0, "pitch": 0.0},
                        "trees": [],
                        "reputation": 0,
                        "tutorialsEnabled": true,
                        "completedTutorialMilestones": [],
                        "acquiredToolIds": ["sprout-spawner"],
                        "orders": [{"orderId": "old", "state": "pending", "pot": null}]
                    }),
                ))
                .await
                .unwrap(),
        )
        .await;
        let slot_id = created["slotId"].as_str().unwrap();

        assert_eq!(
            response_json(
                app.oneshot(request(
                    "/__orchard_playtest/content/orders",
                    json!({
                        "slotId": slot_id,
                        "content": [{
                            "id": "new",
                            "prerequisites": [],
                            "reward": 1,
                            "goal": {
                                "root": "r0",
                                "regions": {
                                    "r0": {"kind": "sheet"},
                                    "outer": {"kind": "cut", "parent": "r0"}
                                },
                                "nodes": {},
                                "wires": {}
                            },
                            "formula": "¬P"
                        }]
                    }),
                ))
                .await
                .unwrap(),
            )
            .await,
            Value::Null
        );
        assert_eq!(
            serde_json::from_slice::<Vec<OrderContentRecord>>(
                &std::fs::read(content_path).unwrap()
            )
            .unwrap(),
            vec![OrderContentRecord {
                id: "new".into(),
                prerequisites: vec![],
                reward: 1,
                goal: json!({
                    "root": "r0",
                    "regions": {
                        "r0": {"kind": "sheet"},
                        "outer": {"kind": "cut", "parent": "r0"}
                    },
                    "nodes": {},
                    "wires": {}
                }),
                formula: Some("¬P".into()),
            }]
        );
        assert_eq!(saves.load(slot_id).unwrap().orders[0].order_id, "new");
    }

    // This catches tutorial/tool route aliasing, save-shaped inputs, and authored writes leaking
    // into the live save database.
    #[tokio::test]
    async fn authored_content_routes_replace_distinct_files_without_mutating_the_live_save() {
        let temporary = tempfile::tempdir().unwrap();
        let saves = SaveStore::new(temporary.path().join("saves"));
        let order_path = temporary.path().join("orders.json");
        let tutorial_path = temporary.path().join("tutorial.json");
        let tool_path = temporary.path().join("tools.json");
        std::fs::write(&order_path, "[]\n").unwrap();
        std::fs::write(&tutorial_path, "[]\n").unwrap();
        std::fs::write(&tool_path, "[]\n").unwrap();
        let app = router_with_content_stores(
            saves.clone(),
            OrderContentStore::new(order_path),
            AuthoredContentStore::new(tutorial_path.clone(), tool_path.clone()),
            config(),
        );
        let created = response_json(
            app.clone()
                .oneshot(request(
                    "/__orchard_playtest/save/create",
                    json!({
                        "displayName": "Authored Content Orchard",
                        "camera": {"x": 0.0, "y": 1.7, "z": 8.0, "yaw": 0.0, "pitch": 0.0},
                        "trees": [],
                        "reputation": 0,
                        "tutorialsEnabled": true,
                        "completedTutorialMilestones": ["move"],
                        "acquiredToolIds": ["sprout-spawner"],
                        "orders": [{"orderId": "old", "state": "pending", "pot": null}]
                    }),
                ))
                .await
                .unwrap(),
        )
        .await;
        let slot_id = created["slotId"].as_str().unwrap();
        let previous_save = saves.load(slot_id).unwrap();
        let tutorial = Value::Array(
            [
                "move", "look", "ascend", "descend", "sprint", "select-tree",
                "move-orbit", "exit-orbit", "spawn-two-sprouts", "acquire-double-cut",
                "apply-double-cut", "double-cut-explained", "acquire-iteration",
                "duplicate-nonblank", "complete-blank-order",
            ]
            .into_iter()
            .map(|milestone_id| {
                json!({"milestoneId": milestone_id, "text": format!("Text for {milestone_id}")})
            })
            .collect(),
        );
        let tools = json!([
            {"id": "sprout-spawner", "name": "Spawner", "description": "Plants sprouts"},
            {"id": "double-cut", "name": "Double Cut", "description": "Cuts twice"},
            {"id": "iteration", "name": "Iteration", "description": "Duplicates trees"}
        ]);

        assert_eq!(
            response_json(
                app.clone()
                    .oneshot(request(
                        "/__orchard_playtest/content/tutorial",
                        json!({"content": tutorial}),
                    ))
                    .await
                    .unwrap(),
            )
            .await,
            Value::Null
        );
        assert_eq!(
            response_json(
                app.oneshot(request(
                    "/__orchard_playtest/content/tools",
                    json!({"content": tools}),
                ))
                .await
                .unwrap(),
            )
            .await,
            Value::Null
        );

        assert_eq!(
            serde_json::from_slice::<Value>(&std::fs::read(tutorial_path).unwrap()).unwrap(),
            tutorial
        );
        assert_eq!(
            serde_json::from_slice::<Value>(&std::fs::read(tool_path).unwrap()).unwrap(),
            tools
        );
        assert_eq!(saves.load(slot_id).unwrap(), previous_save);
    }

    // This catches a save-shaped envelope being silently accepted by a global content route.
    #[tokio::test]
    async fn authored_content_routes_reject_slot_ids_without_touching_content_or_saves() {
        let temporary = tempfile::tempdir().unwrap();
        let saves = SaveStore::new(temporary.path().join("saves"));
        let order_path = temporary.path().join("orders.json");
        let tutorial_path = temporary.path().join("tutorial.json");
        let tool_path = temporary.path().join("tools.json");
        std::fs::write(&order_path, "[]\n").unwrap();
        std::fs::write(&tutorial_path, "tutorial-before\n").unwrap();
        std::fs::write(&tool_path, "tools-before\n").unwrap();
        let app = router_with_content_stores(
            saves.clone(),
            OrderContentStore::new(order_path),
            AuthoredContentStore::new(tutorial_path.clone(), tool_path.clone()),
            config(),
        );
        let tutorial = Value::Array(
            [
                "move",
                "look",
                "ascend",
                "descend",
                "sprint",
                "select-tree",
                "move-orbit",
                "exit-orbit",
                "spawn-two-sprouts",
                "acquire-double-cut",
                "apply-double-cut",
                "double-cut-explained",
                "acquire-iteration",
                "duplicate-nonblank",
                "complete-blank-order",
            ]
            .into_iter()
            .map(|milestone_id| json!({"milestoneId": milestone_id, "text": "Text"}))
            .collect(),
        );
        let tools = json!([
            {"id": "sprout-spawner", "name": "Spawner", "description": "Plants"},
            {"id": "double-cut", "name": "Double Cut", "description": "Cuts"},
            {"id": "iteration", "name": "Iteration", "description": "Duplicates"}
        ]);

        for (path, content) in [
            ("/__orchard_playtest/content/tutorial", tutorial),
            ("/__orchard_playtest/content/tools", tools),
        ] {
            let response = app
                .clone()
                .oneshot(request(
                    path,
                    json!({"slotId": "save-shaped", "content": content}),
                ))
                .await
                .unwrap();
            assert_eq!(response.status(), StatusCode::UNPROCESSABLE_ENTITY);
        }

        assert_eq!(std::fs::read(&tutorial_path).unwrap(), b"tutorial-before\n");
        assert_eq!(std::fs::read(&tool_path).unwrap(), b"tools-before\n");
        assert!(saves.list().unwrap().is_empty());
    }

    // This ignored helper lets the Vite integration test exercise the real authenticated router
    // against its watched fixture paths without changing checked-in content.
    #[tokio::test]
    #[ignore]
    async fn vite_authored_content_server() {
        use std::path::PathBuf;
        use std::time::Duration;

        let port = std::env::var("ORCHARD_TEST_CONTENT_PORT")
            .unwrap()
            .parse::<u16>()
            .unwrap();
        let origin = std::env::var("ORCHARD_TEST_CONTENT_ORIGIN").unwrap();
        let root = PathBuf::from(std::env::var("ORCHARD_TEST_CONTENT_ROOT").unwrap());
        let stop = PathBuf::from(std::env::var("ORCHARD_TEST_CONTENT_STOP").unwrap());
        let app = router_with_content_stores(
            SaveStore::new(root.join("saves")),
            OrderContentStore::new(root.join("orders.json")),
            AuthoredContentStore::new(root.join("tutorial.json"), root.join("tools.json")),
            PlaytestServerConfig {
                token: TOKEN.into(),
                allowed_origin: origin.parse().unwrap(),
            },
        );
        let listener = tokio::net::TcpListener::bind(("127.0.0.1", port))
            .await
            .unwrap();
        axum::serve(listener, app)
            .with_graceful_shutdown(async move {
                while !stop.exists() {
                    tokio::time::sleep(Duration::from_millis(20)).await;
                }
            })
            .await
            .unwrap();
    }

    // This catches accidentally dispatching an unauthorized request to SaveStore.
    #[tokio::test]
    async fn requests_without_the_exact_token_or_origin_never_touch_the_store() {
        let temporary = tempfile::tempdir().unwrap();
        let store = SaveStore::new(temporary.path().to_path_buf());
        let app = router(store.clone(), config());

        let allowed_preflight = Request::builder()
            .method("OPTIONS")
            .uri("/__orchard_playtest/save/create")
            .header(header::ORIGIN, ORIGIN)
            .header(header::ACCESS_CONTROL_REQUEST_METHOD, "POST")
            .header(
                header::ACCESS_CONTROL_REQUEST_HEADERS,
                "content-type, x-orchard-playtest-token",
            )
            .body(Body::empty())
            .unwrap();
        let allowed_preflight_response = app.clone().oneshot(allowed_preflight).await.unwrap();
        assert_eq!(allowed_preflight_response.status(), StatusCode::OK);
        assert_eq!(
            allowed_preflight_response
                .headers()
                .get(header::ACCESS_CONTROL_ALLOW_ORIGIN),
            Some(&HeaderValue::from_static(ORIGIN))
        );

        let wrong_origin_preflight = Request::builder()
            .method("OPTIONS")
            .uri("/__orchard_playtest/save/create")
            .header(header::ORIGIN, "http://127.0.0.1:31337")
            .header(header::ACCESS_CONTROL_REQUEST_METHOD, "POST")
            .header(
                header::ACCESS_CONTROL_REQUEST_HEADERS,
                "content-type, x-orchard-playtest-token",
            )
            .body(Body::empty())
            .unwrap();
        assert_eq!(
            app.clone()
                .oneshot(wrong_origin_preflight)
                .await
                .unwrap()
                .status(),
            StatusCode::FORBIDDEN
        );

        for request in [
            Request::builder()
                .method("POST")
                .uri("/__orchard_playtest/save/create")
                .header(header::ORIGIN, ORIGIN)
                .header(header::CONTENT_TYPE, "application/json")
                .body(Body::from("{}"))
                .unwrap(),
            Request::builder()
                .method("POST")
                .uri("/__orchard_playtest/save/create")
                .header(header::ORIGIN, ORIGIN)
                .header("x-orchard-playtest-token", "wrong-token")
                .header(header::CONTENT_TYPE, "application/json")
                .body(Body::from("{}"))
                .unwrap(),
        ] {
            assert_eq!(
                app.clone().oneshot(request).await.unwrap().status(),
                StatusCode::UNAUTHORIZED
            );
        }

        let wrong_origin = Request::builder()
            .method("POST")
            .uri("/__orchard_playtest/save/create")
            .header(header::ORIGIN, "http://127.0.0.1:31337")
            .header("x-orchard-playtest-token", TOKEN)
            .header(header::CONTENT_TYPE, "application/json")
            .body(Body::from("{}"))
            .unwrap();
        assert_eq!(
            app.oneshot(wrong_origin).await.unwrap().status(),
            StatusCode::FORBIDDEN
        );
        assert!(store.list().unwrap().is_empty());
    }
}
