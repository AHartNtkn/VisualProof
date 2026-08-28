#!/usr/bin/env bash
set -euo pipefail

token="$(node --input-type=module --eval 'console.log(crypto.randomUUID())')"
save_dir="${ORCHARD_PLAYTEST_SAVE_DIR:-src-tauri/target/browser-playtest-saves}"
service_pid=''

cleanup() {
  if [[ -n "$service_pid" ]]; then
    kill "$service_pid" 2>/dev/null || true
    wait "$service_pid" 2>/dev/null || true
  fi
}
trap cleanup EXIT INT TERM

cargo build --manifest-path src-tauri/Cargo.toml --features playtest-server --bin orchard_playtest_server

ORCHARD_PLAYTEST_TOKEN="$token" \
ORCHARD_PLAYTEST_ORIGIN='http://127.0.0.1:1420' \
ORCHARD_PLAYTEST_SAVE_DIR="$save_dir" \
ORCHARD_PLAYTEST_PORT='1421' \
src-tauri/target/debug/orchard_playtest_server &
service_pid=$!

for _ in {1..100}; do
  if curl --silent --fail \
    --header 'Origin: http://127.0.0.1:1420' \
    --header "x-orchard-playtest-token: $token" \
    'http://127.0.0.1:1421/__orchard_playtest/health' >/dev/null; then
    break
  fi
  sleep 0.1
done

if ! curl --silent --fail \
  --header 'Origin: http://127.0.0.1:1420' \
  --header "x-orchard-playtest-token: $token" \
  'http://127.0.0.1:1421/__orchard_playtest/health' >/dev/null; then
  echo 'orchard playtest save service did not become ready' >&2
  exit 1
fi

VITE_ORCHARD_SAVE_TRANSPORT='playtest-http' \
VITE_ORCHARD_PLAYTEST_URL='http://127.0.0.1:1421' \
VITE_ORCHARD_PLAYTEST_TOKEN="$token" \
npm run game
