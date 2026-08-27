#!/usr/bin/env bash
set -euo pipefail

mode=${1:-e2e}
data_roots=()
smoke_pid=

cleanup() {
  if [[ -n "$smoke_pid" ]] && kill -0 "$smoke_pid" 2>/dev/null; then
    kill "$smoke_pid"
    wait "$smoke_pid" 2>/dev/null || true
  fi
  for root in "${data_roots[@]}"; do
    case "$root" in
      /tmp/orchard-game-e2e.*) rm -rf -- "$root" ;;
    esac
  done
}

run_smoke_window() {
  local data_root=$1
  XDG_DATA_HOME="$data_root" GDK_BACKEND=x11 src-tauri/target/release/orchard-game &
  smoke_pid=$!
  for _ in {1..100}; do
    if xdotool search --name '^Orchard$' >/dev/null 2>&1; then
      echo "native Orchard window opened on private X11 display"
      kill "$smoke_pid"
      wait "$smoke_pid" 2>/dev/null || true
      smoke_pid=
      return
    fi
    if ! kill -0 "$smoke_pid" 2>/dev/null; then
      wait "$smoke_pid"
      echo "Orchard exited before opening a native window" >&2
      exit 1
    fi
    sleep .1
  done
  echo "Orchard did not open a native window" >&2
  exit 1
}
trap cleanup EXIT

new_data_root() {
  current_data_root=$(mktemp -d /tmp/orchard-game-e2e.XXXXXX)
  data_roots+=("$current_data_root")
}

run_scenario() {
  local scenario=$1
  local phase=${2:-}
  local data_root=$3
  xvfb-run -a -s '-screen 0 1600x1000x24' env -u WAYLAND_DISPLAY \
    GAME_E2E_PRIVATE_X11=1 GAME_E2E_SCENARIO="$scenario" GAME_E2E_PHASE="$phase" \
    GAME_E2E_DATA_ROOT="$data_root" GDK_BACKEND=x11 \
    node_modules/.bin/wdio run game/wdio.conf.ts
}

case "$mode" in
  e2e)
    npm run build:game:e2e
    new_data_root
    run_scenario camera camera "$current_data_root"
    for phase in seedling-read large-write large-read; do
      run_scenario double-cut "$phase" "$current_data_root"
    done
    ;;
  stress)
    npm run build:game:e2e
    for count in 10 50 100 250 500 1000 2000; do
      new_data_root
      run_scenario "stress-$count" stress "$current_data_root"
    done
    ;;
  smoke)
    if ! build_output=$(npm run build:game:desktop -- --no-bundle 2>&1); then
      echo "$build_output"
      exit 1
    fi
    echo "$build_output"
    if [[ "$build_output" != *"target/release/orchard-game"* ]]; then
      echo "Tauri did not report orchard-game as the built application" >&2
      exit 1
    fi
    new_data_root
    xvfb-run -a -s '-screen 0 1600x1000x24' env -u WAYLAND_DISPLAY \
      GAME_E2E_PRIVATE_X11=1 GDK_BACKEND=x11 "$0" smoke-window "$current_data_root"
    ;;
  smoke-window)
    if [[ ${GAME_E2E_PRIVATE_X11:-} != 1 || -z ${DISPLAY:-} ]]; then
      echo "smoke-window requires a private X11 display" >&2
      exit 2
    fi
    run_smoke_window "$2"
    ;;
  *)
    echo "usage: $0 {e2e|stress|smoke}" >&2
    exit 2
    ;;
esac
