#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
mode=${1:-}
violations=0

module_file() {
  printf '%s/%s.lean\n' "$repo_root" "${1//./\/}"
}

module_exists() {
  [[ -f "$(module_file "$1")" ]]
}

imports_of() {
  awk '$1 == "import" { for (i = 2; i <= NF; i++) print $i }' \
    "$(module_file "$1")"
}

declare -A seen=()

walk_rules() {
  local module=$1
  local path=$2
  if [[ -n ${seen[$module]+x} ]]; then
    return 0
  fi
  seen[$module]=1

  local imported
  while IFS= read -r imported; do
    [[ $imported == VisualProof || $imported == VisualProof.* ]] || continue
    case "$imported" in
      VisualProof.Concrete|VisualProof.Concrete.*|\
      VisualProof.Refinement|VisualProof.Refinement.*|\
      VisualProof.Proof|VisualProof.Proof.*|\
      VisualProof.Rule.Executable|VisualProof.Rule.Executable.*)
        printf 'forbidden rule dependency: %s -> %s\n' "$path" "$imported"
        violations=$((violations + 1))
        ;;
      *)
        if module_exists "$imported"; then
          walk_rules "$imported" "$path -> $imported"
        fi
        ;;
    esac
  done < <(imports_of "$module")
}

audit_rules() {
  local root
  for root in VisualProof.Rule.Step VisualProof.Rule.Soundness; do
    if ! module_exists "$root"; then
      printf 'missing recursive authority root: %s\n' "$root"
      violations=$((violations + 1))
    else
      walk_rules "$root" "$root"
    fi
  done

  if (( violations > 0 )); then
    printf 'rules: %d violation(s)\n' "$violations" >&2
    return 1
  fi
  printf 'rules: clean recursive authority closure\n'
}

audit_roster() {
  local step="$repo_root/VisualProof/Rule/Step.lean"
  local expected=$'erasure\nwireSever\niteration\ndoubleCut\nvacuity'
  local actual
  actual=$(awk '
    /^inductive Step / { inside = 1; next }
    inside && /^theorem / { exit }
    inside && /^[[:space:]]*\|[[:space:]]*[[:alpha:]][[:alnum:]_]*/ {
      line = $0
      sub(/^[[:space:]]*\|[[:space:]]*/, "", line)
      sub(/[[:space:]].*$/, "", line)
      print line
    }
  ' "$step")

  if [[ $actual != "$expected" ]]; then
    printf 'Rule.Step roster mismatch\nexpected:\n%s\nactual:\n%s\n' \
      "$expected" "$actual" >&2
    return 1
  fi
  if rg -n '\|[[:space:]]*comprehension\b' "$step"; then
    printf 'Comprehension must remain outside Rule.Step\n' >&2
    return 1
  fi
  printf 'roster: exact five Rule.Step constructors; Comprehension remains separate\n'
}

audit_implementation() {
  local root="$repo_root/VisualProof/Rule/Executable"
  local umbrella="$repo_root/VisualProof/Rule/Executable.lean"
  if [[ ! -d $root || ! -f $umbrella ]]; then
    printf 'implementation: executable authority is not installed yet\n' >&2
    return 1
  fi

  local match
  while IFS= read -r match; do
    [[ -n $match ]] || continue
    printf 'forbidden executable dependency: %s\n' "$match"
    violations=$((violations + 1))
  done < <(rg -n '^import VisualProof\.(Model|Diagram\.Semantics($|\.)|Rule\.Soundness($|\.)|Concrete($|\.)|Refinement($|\.)|Proof($|\.))' \
    "$root" "$umbrella" || true)

  if (( violations > 0 )); then
    printf 'implementation: %d violation(s)\n' "$violations" >&2
    return 1
  fi
  printf 'implementation: clean executable dependency boundary\n'
}

audit_documentation() {
  local goal="$repo_root/docs/goals/recursive-rewrite-authority/goal.md"
  local state="$repo_root/docs/goals/recursive-rewrite-authority/state.yaml"
  if [[ ! -f $goal || ! -f $state ]]; then
    printf 'missing active recursive execution goal authority\n' >&2
    return 1
  fi
  if rg -n '(flat representation|graph execution authority|refinement layer|concrete executor)' \
      "$goal" "$state"; then
    printf 'active goal still assigns authority to an obsolete execution model\n' >&2
    return 1
  fi
  printf 'documentation: recursive indexed execution is the active authority\n'
}

case "$mode" in
  rules) audit_rules ;;
  roster) audit_roster ;;
  implementation) audit_implementation ;;
  documentation) audit_documentation ;;
  *)
    printf 'usage: %s {rules|roster|implementation|documentation}\n' "$0" >&2
    exit 2
    ;;
esac
