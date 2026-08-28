use axum::http::{HeaderValue, Uri};
use orchard_game::{
    playtest_server::{router, PlaytestServerConfig},
    save_store::SaveStore,
};
use std::{
    env,
    net::{IpAddr, Ipv4Addr, SocketAddr},
    path::PathBuf,
};

#[tokio::main]
async fn main() {
    if let Err(error) = run().await {
        eprintln!("orchard_playtest_server: {error}");
        std::process::exit(1);
    }
}

async fn run() -> Result<(), String> {
    let token = required_environment("ORCHARD_PLAYTEST_TOKEN")?;
    HeaderValue::from_str(&token)
        .map_err(|_| "ORCHARD_PLAYTEST_TOKEN must be a valid HTTP header value".to_owned())?;
    let origin = parse_loopback_origin(&required_environment("ORCHARD_PLAYTEST_ORIGIN")?)?;
    let save_directory = PathBuf::from(required_environment("ORCHARD_PLAYTEST_SAVE_DIR")?);
    let port = parse_port(&required_environment("ORCHARD_PLAYTEST_PORT")?)?;
    let address = SocketAddr::new(IpAddr::V4(Ipv4Addr::LOCALHOST), port);
    let listener = tokio::net::TcpListener::bind(address)
        .await
        .map_err(|error| format!("could not bind {address}: {error}"))?;

    axum::serve(
        listener,
        router(
            SaveStore::new(save_directory),
            PlaytestServerConfig {
                token,
                allowed_origin: origin,
            },
        ),
    )
    .await
    .map_err(|error| format!("playtest server stopped unexpectedly: {error}"))
}

fn required_environment(name: &str) -> Result<String, String> {
    let value = env::var(name).map_err(|_| format!("{name} is required"))?;
    if value.trim().is_empty() {
        return Err(format!("{name} must not be empty"));
    }
    Ok(value)
}

fn parse_loopback_origin(value: &str) -> Result<HeaderValue, String> {
    if value == "*" {
        return Err("ORCHARD_PLAYTEST_ORIGIN must not be a wildcard".to_owned());
    }
    let uri = value
        .parse::<Uri>()
        .map_err(|_| "ORCHARD_PLAYTEST_ORIGIN must be a valid origin".to_owned())?;
    if !matches!(uri.scheme_str(), Some("http") | Some("https"))
        || uri.authority().is_none()
        || uri.path() != "/"
        || uri.query().is_some()
        || value.ends_with('/')
    {
        return Err(
            "ORCHARD_PLAYTEST_ORIGIN must be an http or https origin without a path".to_owned(),
        );
    }
    let host = uri
        .host()
        .ok_or_else(|| "ORCHARD_PLAYTEST_ORIGIN must include a host".to_owned())?;
    let address = host
        .trim_matches(['[', ']'])
        .parse::<IpAddr>()
        .map_err(|_| "ORCHARD_PLAYTEST_ORIGIN must use a loopback IP address".to_owned())?;
    if !address.is_loopback() {
        return Err("ORCHARD_PLAYTEST_ORIGIN must use a loopback IP address".to_owned());
    }
    HeaderValue::from_str(value)
        .map_err(|_| "ORCHARD_PLAYTEST_ORIGIN must be a valid HTTP header value".to_owned())
}

fn parse_port(value: &str) -> Result<u16, String> {
    let port = value
        .parse::<u16>()
        .map_err(|_| "ORCHARD_PLAYTEST_PORT must be an integer between 1 and 65535".to_owned())?;
    if port == 0 {
        return Err("ORCHARD_PLAYTEST_PORT must be an integer between 1 and 65535".to_owned());
    }
    Ok(port)
}
