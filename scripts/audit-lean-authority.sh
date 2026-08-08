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
         $imported == VisualProof.Refinement.Implementation.* ||
         $imported == VisualProof.Refinement.Step.* ||
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
declare -A reached=()
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

constructors_between() {
  local file=$1
  local start=$2
  local stop=$3

  awk -v start="$start" -v stop="$stop" '
    $0 ~ start { inside = 1; next }
    inside && $0 ~ stop { exit }
    inside && /^[[:space:]]*\|[[:space:]]*[[:alpha:]][[:alnum:]_]*/ {
      line = $0
      sub(/^[[:space:]]*\|[[:space:]]*/, "", line)
      sub(/[[:space:]].*$/, "", line)
      print line
    }
  ' "$file"
}

case_labels_between() {
  local file=$1
  local start=$2
  local stop=$3

  awk -v start="$start" -v stop="$stop" '
    $0 ~ start { inside = 1; next }
    inside && $0 ~ stop { exit }
    inside && /^[[:space:]]*\|[[:space:]]*\.[[:alpha:]][[:alnum:]_]*/ {
      line = $0
      sub(/^[[:space:]]*\|[[:space:]]*\./, "", line)
      sub(/[[:space:]].*$/, "", line)
      print line
    }
  ' "$file"
}

tags_in_all() {
  local file=$1
  awk '
    /^def StepTag[.]all[[:space:]]*:/ { inside = 1; next }
    inside && /^theorem StepTag\.all_length/ { exit }
    inside {
      line = $0
      while (match(line, /\.[[:alpha:]][[:alnum:]_]*/)) {
        print substr(line, RSTART + 1, RLENGTH - 1)
        line = substr(line, RSTART + RLENGTH)
      }
    }
  ' "$file"
}

assert_exact_roster() {
  local label=$1
  shift
  local -a expected=("$@")
  local -a actual=()
  mapfile -t actual

  local expected_sorted actual_sorted duplicate
  expected_sorted=$(printf '%s\n' "${expected[@]}" | LC_ALL=C sort)
  actual_sorted=$(printf '%s\n' "${actual[@]}" | LC_ALL=C sort)
  duplicate=$(printf '%s\n' "${actual[@]}" | LC_ALL=C sort | uniq -d)

  if [[ ${#actual[@]} -ne ${#expected[@]} || $actual_sorted != "$expected_sorted" || -n $duplicate ]]; then
    printf '%s roster mismatch\nexpected:\n%s\nactual:\n%s\n' \
      "$label" "$expected_sorted" "$actual_sorted"
    if [[ -n $duplicate ]]; then
      printf '%s duplicate constructor/tag(s): %s\n' "$label" "$duplicate"
    fi
    violations=$((violations + 1))
  fi
}

require_roster_file() {
  local file=$1
  if [[ ! -f $file ]]; then
    printf 'missing roster source: %s\n' "${file#"$repo_root"/}"
    violations=$((violations + 1))
    return 1
  fi
}

require_roster_declaration() {
  local label=$1
  local pattern=$2
  local file=$3
  if ! rg -q --pcre2 "$pattern" "$file"; then
    printf 'missing required standalone declaration: %s\n' "$label"
    violations=$((violations + 1))
  fi
}

require_roster_namespaced_theorem() {
  local target_namespace=$1
  local theorem=$2
  local file=$3

  if ! awk -v target_namespace="$target_namespace" -v theorem="$theorem" '
    /^namespace [[:alnum:]_.]+$/ {
      namespaces[++depth] = $2
      next
    }
    /^end [[:alnum:]_.]+$/ {
      if (depth > 0 && namespaces[depth] == $2) depth--
      next
    }
    $1 == "theorem" && $2 == theorem && depth > 0 &&
        namespaces[depth] == target_namespace {
      found = 1
    }
    END { exit !found }
  ' "$file"; then
    printf 'missing required standalone declaration: %s.%s\n' "$target_namespace" "$theorem"
    violations=$((violations + 1))
  fi
}

reject_roster_matches() {
  local label=$1
  local pattern=$2
  shift 2

  local -a existing=()
  local root match
  for root in "$@"; do
    [[ -e $root ]] && existing+=("$root")
  done
  (( ${#existing[@]} > 0 )) || return

  while IFS= read -r match; do
    [[ -n $match ]] || continue
    printf '%s: %s\n' "$label" "$match"
    violations=$((violations + 1))
  done < <(rg -n -i --glob '*.lean' "$pattern" "${existing[@]}" || true)
}

audit_roster() {
  local rule_step="$repo_root/VisualProof/Rule/Step.lean"
  local concrete_step="$repo_root/VisualProof/Concrete/Step.lean"
  local step_core="$repo_root/VisualProof/Concrete/Step/Core.lean"
  local step_tags="$repo_root/VisualProof/Concrete/StepTags.lean"
  local comprehension_relation="$repo_root/VisualProof/Rule/Comprehension/Relation.lean"
  local comprehension_soundness="$repo_root/VisualProof/Rule/Soundness/Comprehension.lean"
  local -a rule_expected=(erasure wireSever iteration doubleCut vacuity)
  local -a concrete_expected=(boundRelationSpawn wireJoin erasure wireSever iteration deiteration doubleCutIntro doubleCutElim vacuousIntro vacuousElim)

  require_roster_file "$rule_step" &&
    assert_exact_roster 'Rule.Step constructors' "${rule_expected[@]}" \
      < <(constructors_between "$rule_step" '^inductive Step[[:space:]]' '^theorem Step[.]iso')
  require_roster_file "$concrete_step" &&
    assert_exact_roster 'Concrete.Step constructors' "${concrete_expected[@]}" \
      < <(constructors_between "$concrete_step" '^inductive Step[[:space:]]' '^def Step[.]tag')
  require_roster_file "$concrete_step" &&
    assert_exact_roster 'Concrete.Step.tag cases' "${concrete_expected[@]}" \
      < <(case_labels_between "$concrete_step" '^def Step[.]tag' '^theorem Step[.]tag_mem_all')
  require_roster_file "$step_core" &&
    assert_exact_roster 'Concrete.StepTag constructors' "${concrete_expected[@]}" \
      < <(constructors_between "$step_core" '^inductive StepTag$' '^def StepTag[.]all')
  require_roster_file "$step_core" &&
    assert_exact_roster 'Concrete.StepTag.all tags' "${concrete_expected[@]}" \
      < <(tags_in_all "$step_core")
  require_roster_file "$step_tags" &&
    assert_exact_roster 'Concrete.StepTag serialized tags' "${concrete_expected[@]}" \
      < <(case_labels_between "$step_tags" '^def serializedName' '^def serializedAll')

  require_roster_file "$comprehension_relation" &&
    require_roster_declaration 'Comprehension relation' \
      '(?m)^def Comprehension[[:space:]]*:[[:space:]]*Rule' "$comprehension_relation"
  require_roster_file "$comprehension_relation" &&
    require_roster_declaration 'Comprehension isomorphism transport' \
      '(?m)^theorem Comprehension\.iso\b' "$comprehension_relation"
  require_roster_file "$comprehension_soundness" &&
    require_roster_namespaced_theorem Comprehension sound "$comprehension_soundness"

  reject_roster_matches 'Comprehension execution declaration' '\bcomprehension\b' \
    "$repo_root/VisualProof/Concrete" "$repo_root/VisualProof/Refinement"
  reject_roster_matches 'Comprehension branch' '\bcomprehension\b' \
    "$rule_step" "$repo_root/VisualProof/Refinement/Step" \
    "$repo_root/VisualProof/Refinement/Step.lean" \
    "$repo_root/VisualProof/Refinement/Complete" \
    "$repo_root/VisualProof/Refinement/Complete.lean" \
    "$repo_root/VisualProof/Refinement/Means.lean"
  reject_roster_matches 'obsolete Proof request name' \
    'comprehension(Abstract|Instantiate)' "$repo_root/VisualProof/Proof"

  if (( violations > 0 )); then
    printf 'roster: %d execution-roster/absence violation(s)\n' "$violations" >&2
    return 1
  fi

  printf 'roster: exact five-family Rule.Step and ten-constructor Concrete.Step roster; standalone Comprehension only\n'
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
  reached[$module]=1

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

if [[ $mode == roster ]]; then
  audit_roster
  exit $?
fi

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
      VisualProof.Refinement.Step
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
    printf 'usage: %s {rules|implementation|proof|roster}\n' "$0" >&2
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

if [[ $mode == proof ]]; then
  for interface in VisualProof.Refinement.Step VisualProof.Rule.Soundness; do
    if [[ -z ${reached[$interface]+x} ]]; then
      printf 'proof closure does not reach required aggregate: %s\n' "$interface"
      violations=$((violations + 1))
    fi
  done
fi

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
