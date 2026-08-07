#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
mode=${1:-}

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

is_forbidden() {
  local importer=$1
  local imported=$2

  case "$mode" in
    rules)
      [[ $imported == VisualProof.Concrete ||
         $imported == VisualProof.Concrete.* ||
         $imported == VisualProof.Refinement ||
         $imported == VisualProof.Refinement.* ||
         $imported == VisualProof.Proof ||
         $imported == VisualProof.Proof.* ]]
      ;;
    implementation)
      [[ $imported == VisualProof.Model ||
         $imported == VisualProof.Diagram.Semantics ||
         $imported == VisualProof.Diagram.Semantics.* ||
         $imported == VisualProof.Concrete.Semantics ||
         $imported == VisualProof.Concrete.*.Semantics ||
         $imported == VisualProof.Concrete.*.Semantics.* ||
         $imported == VisualProof.Concrete.Elaboration.Simulation ||
         $imported == VisualProof.Rule.Soundness ||
         $imported == VisualProof.Rule.Soundness.* ||
         $imported == VisualProof.Proof ||
         $imported == VisualProof.Proof.* ]]
      ;;
    proof)
      [[ $imported == VisualProof.Concrete.Semantics ||
         $imported == VisualProof.Concrete.*.Semantics ||
         $imported == VisualProof.Concrete.*.Semantics.* ||
         $imported == VisualProof.Concrete.Elaboration.Simulation ||
         $imported == VisualProof.Refinement.Implementation.Soundness ||
         $imported == VisualProof.Rule.Soundness.* ]]
      ;;
  esac
}

is_opaque_proof_interface() {
  [[ $mode == proof &&
     ($1 == VisualProof.Rule.Soundness ||
      $1 == VisualProof.Refinement.Step) ]]
}

declare -A seen=()
violations=0

report_source_matches() {
  local label=$1
  local pattern=$2
  shift 2

  local match
  while IFS= read -r match; do
    [[ -n $match ]] || continue
    printf '%s: %s\n' "$label" "$match"
    violations=$((violations + 1))
  done < <(rg -n --glob '*.lean' "$pattern" "$@" || true)
}

walk() {
  local root=$1
  local module=$2
  local path=$3
  local key="$root|$module"

  if [[ -n ${seen[$key]+x} ]]; then
    return
  fi
  seen[$key]=1

  if is_opaque_proof_interface "$module"; then
    return
  fi

  local imported
  while IFS= read -r imported; do
    [[ $imported == VisualProof || $imported == VisualProof.* ]] || continue
    if is_forbidden "$module" "$imported"; then
      printf '%s\n' "$path -> $imported"
      violations=$((violations + 1))
    elif module_exists "$imported"; then
      walk "$root" "$imported" "$path -> $imported"
    fi
  done < <(imports_of "$module")
}

case "$mode" in
  rules)
    roots=(
      VisualProof.Rule.Erasure
      VisualProof.Rule.WireSever
      VisualProof.Rule.Iteration
      VisualProof.Rule.DoubleCut
      VisualProof.Rule.Comprehension.Relation
      VisualProof.Rule.Vacuity
      VisualProof.Rule.Soundness.Erasure
      VisualProof.Rule.Soundness.WireSever
      VisualProof.Rule.Soundness.Iteration
      VisualProof.Rule.Soundness.DoubleCut
      VisualProof.Rule.Soundness.Comprehension
      VisualProof.Rule.Soundness.Vacuity
      VisualProof.Rule.Step
      VisualProof.Rule.Soundness
    )
    required_roots=("${roots[@]}")
    ;;
  implementation)
    roots=(
      VisualProof.Concrete.Step
      VisualProof.Concrete.Translate
      VisualProof.Concrete.Encode
      VisualProof.Refinement.Represents
      VisualProof.Refinement.Step
      VisualProof.Refinement.Complete
      VisualProof.Refinement.Rejection
    )
    required_roots=(
      VisualProof.Concrete.Step
      VisualProof.Concrete.Translate
      VisualProof.Concrete.Encode
      VisualProof.Refinement.Represents
    )
    ;;
  proof)
    roots=(
      VisualProof.Proof.Schema
      VisualProof.Proof.Theorem
      VisualProof.Proof.Theory
    )
    required_roots=("${roots[@]}")
    ;;
  *)
    printf 'usage: %s {rules|implementation|proof}\n' "$0" >&2
    exit 2
    ;;
esac

for root in "${required_roots[@]}"; do
  if ! module_exists "$root"; then
    printf 'missing required root: %s\n' "$root"
    violations=$((violations + 1))
  fi
done

root_count=0
for root in "${roots[@]}"; do
  if module_exists "$root"; then
    root_count=$((root_count + 1))
    walk "$root" "$root" "$root"
  fi
done

if [[ $mode == implementation ]]; then
  report_source_matches forbidden-semantic-import \
    '^import VisualProof\.(Model|Diagram\.Semantics($|\.)|Concrete\.Semantics($|\.)|Rule\.Soundness($|\.)|Proof($|\.))' \
    "$repo_root/VisualProof/Concrete" "$repo_root/VisualProof/Refinement"
  report_source_matches forbidden-semantic-declaration \
    '\b(Model|denoteOpen|denoteRegion|ConcreteSemanticSimulation|SuccessfulReceiptSound)\b|Rule\.Step\.sound' \
    "$repo_root/VisualProof/Concrete" "$repo_root/VisualProof/Refinement"
fi

if (( violations > 0 )); then
  printf '%s: %d forbidden import path(s) from %d root(s)\n' \
    "$mode" "$violations" "$root_count" >&2
  exit 1
fi

printf '%s: clean recursive source-import closure across %d root(s)\n' \
  "$mode" "$root_count"
