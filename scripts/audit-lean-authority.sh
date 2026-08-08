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

step_tag_pairs_between() {
  local file=$1
  local start=$2
  local stop=$3

  awk -v start="$start" -v stop="$stop" '
    $0 ~ start { inside = 1; next }
    inside && $0 ~ stop { exit }
    inside && /^[[:space:]]*\|[[:space:]]*\.[[:alpha:]][[:alnum:]_]*/ {
      left = $0
      sub(/^[[:space:]]*\|[[:space:]]*\./, "", left)
      sub(/[[:space:]].*$/, "", left)
      right = $0
      sub(/^.*=>[[:space:]]*\./, "", right)
      sub(/[^[:alnum:]_].*$/, "", right)
      if (right != "") print left " -> " right
    }
  ' "$file"
}

serialized_tag_pairs_between() {
  local file=$1
  local start=$2
  local stop=$3

  awk -v start="$start" -v stop="$stop" '
    $0 ~ start { inside = 1; next }
    inside && $0 ~ stop { exit }
    inside && /^[[:space:]]*\|[[:space:]]*\.[[:alpha:]][[:alnum:]_]*/ {
      left = $0
      sub(/^[[:space:]]*\|[[:space:]]*\./, "", left)
      sub(/[[:space:]].*$/, "", left)
      right = $0
      sub(/^.*=>[[:space:]]*"/, "", right)
      sub(/".*$/, "", right)
      if (right != "") print left " -> " right
    }
  ' "$file"
}

default_cases_between() {
  local file=$1
  local start=$2
  local stop=$3

  awk -v start="$start" -v stop="$stop" '
    $0 ~ start { inside = 1; next }
    inside && $0 ~ stop { exit }
    inside && /^[[:space:]]*\|[[:space:]]*_/ { print }
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

  local expected_ordered actual_ordered duplicate
  expected_ordered=$(printf '%s\n' "${expected[@]}")
  actual_ordered=$(printf '%s\n' "${actual[@]}")
  duplicate=$(printf '%s\n' "${actual[@]}" | LC_ALL=C sort | uniq -d)

  if [[ ${#actual[@]} -ne ${#expected[@]} || $actual_ordered != "$expected_ordered" || -n $duplicate ]]; then
    printf '%s roster mismatch\nexpected:\n%s\nactual:\n%s\n' \
      "$label" "$expected_ordered" "$actual_ordered"
    if [[ -n $duplicate ]]; then
      printf '%s duplicate constructor/tag(s): %s\n' "$label" "$duplicate"
    fi
    violations=$((violations + 1))
  fi
}

reject_default_cases() {
  local label=$1
  local file=$2
  local start=$3
  local stop=$4
  local default_case

  while IFS= read -r default_case; do
    [[ -n $default_case ]] || continue
    printf '%s wildcard/default case: %s\n' "$label" "$default_case"
    violations=$((violations + 1))
  done < <(default_cases_between "$file" "$start" "$stop")
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

lean_code_matches() {
  local pattern=$1
  shift

  local -a roots=("$@")
  local -a files=()
  mapfile -t files < <(rg --files -g '*.lean' "${roots[@]}" 2>/dev/null || true)
  (( ${#files[@]} > 0 )) || return 0

  awk -v pattern="$pattern" '
    function without_comments(line,    out, position, pair, char) {
      out = ""
      position = 1
      while (position <= length(line)) {
        pair = substr(line, position, 2)
        char = substr(line, position, 1)
        if (comment_depth > 0) {
          if (pair == "/-") {
            comment_depth++
            position += 2
          } else if (pair == "-/") {
            comment_depth--
            position += 2
          } else {
            position++
          }
        } else if (pair == "/-") {
          comment_depth = 1
          position += 2
        } else if (pair == "--") {
          break
        } else {
          out = out char
          position++
        }
      }
      return out
    }
    BEGIN { IGNORECASE = 1 }
    {
      code = without_comments($0)
      if (code ~ pattern) printf "%s:%d:%s\n", FILENAME, FNR, code
    }
  ' "${files[@]}"
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
  (( ${#existing[@]} > 0 )) || return 0

  while IFS= read -r match; do
    [[ -n $match ]] || continue
    printf '%s: %s\n' "$label" "$match"
    violations=$((violations + 1))
  done < <(lean_code_matches "$pattern" "${existing[@]}")
}

reject_roster_paths() {
  local label=$1
  shift

  local root path
  for root in "$@"; do
    [[ -d $root ]] || continue
    while IFS= read -r path; do
      [[ -n $path ]] || continue
      printf '%s: %s\n' "$label" "${path#"$repo_root"/}"
      violations=$((violations + 1))
    done < <(find "$root" -type f \
      \( -iname '*comprehension*.lean' -o -iname '*abstraction*.lean' -o -iname '*instantiat*.lean' \) \
      -print | LC_ALL=C sort)
  done
}

means_request_cases() {
  local file=$1

  awk '
    /match[[:space:]]+request[[:space:]]+with/ {
      in_request_match = 1
      next
    }
    in_request_match && /^[[:space:]]*\|[[:space:]]*\./ {
      line = $0
      match(line, /^[[:space:]]*/)
      indentation = RLENGTH
      if (!branch_indentation_set) {
        branch_indentation = indentation
        branch_indentation_set = 1
      }
      if (indentation != branch_indentation) next
      sub(/^[[:space:]]*\|[[:space:]]*\./, "", line)
      sub(/[[:space:]].*$/, "", line)
      print line
    }
  ' "$file"
}

means_request_default_cases() {
  local file=$1

  awk '
    /match[[:space:]]+request[[:space:]]+with/ {
      in_request_match = 1
      next
    }
    in_request_match && /^[[:space:]]*\|/ {
      line = $0
      match(line, /^[[:space:]]*/)
      indentation = RLENGTH
      if (!branch_indentation_set) {
        branch_indentation = indentation
        branch_indentation_set = 1
      }
      if (indentation == branch_indentation && line ~ /^[[:space:]]*\|[[:space:]]*_/) print line
    }
  ' "$file"
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
  local -a concrete_tag_expected=()
  local tag
  for tag in "${concrete_expected[@]}"; do
    concrete_tag_expected+=("$tag -> $tag")
  done

  require_roster_file "$rule_step" &&
    assert_exact_roster 'Rule.Step constructors' "${rule_expected[@]}" \
      < <(constructors_between "$rule_step" '^inductive Step[[:space:]]' '^theorem Step[.]iso')
  require_roster_file "$concrete_step" &&
    assert_exact_roster 'Concrete.Step constructors' "${concrete_expected[@]}" \
      < <(constructors_between "$concrete_step" '^inductive Step[[:space:]]' '^def Step[.]tag')
  require_roster_file "$concrete_step" &&
    assert_exact_roster 'Concrete.Step.tag constructor-to-tag cases' "${concrete_tag_expected[@]}" \
      < <(step_tag_pairs_between "$concrete_step" '^def Step[.]tag' '^theorem Step[.]tag_mem_all')
  require_roster_file "$concrete_step" &&
    reject_default_cases 'Concrete.Step.tag' "$concrete_step" \
      '^def Step[.]tag' '^theorem Step[.]tag_mem_all'
  require_roster_file "$step_core" &&
    assert_exact_roster 'Concrete.StepTag constructors' "${concrete_expected[@]}" \
      < <(constructors_between "$step_core" '^inductive StepTag$' '^def StepTag[.]all')
  require_roster_file "$step_core" &&
    assert_exact_roster 'Concrete.StepTag.all tags' "${concrete_expected[@]}" \
      < <(tags_in_all "$step_core")
  require_roster_file "$step_tags" &&
    assert_exact_roster 'Concrete.StepTag serialized tag-name cases' "${concrete_tag_expected[@]}" \
      < <(serialized_tag_pairs_between "$step_tags" '^def serializedName' '^def serializedAll')
  require_roster_file "$step_tags" &&
    reject_default_cases 'Concrete.StepTag.serializedName' "$step_tags" \
      '^def serializedName' '^def serializedAll'

  require_roster_file "$comprehension_relation" &&
    require_roster_declaration 'Comprehension relation' \
      '(?m)^def Comprehension[[:space:]]*:[[:space:]]*Rule' "$comprehension_relation"
  require_roster_file "$comprehension_relation" &&
    require_roster_declaration 'Comprehension isomorphism transport' \
      '(?m)^theorem Comprehension\.iso\b' "$comprehension_relation"
  require_roster_file "$comprehension_soundness" &&
    require_roster_namespaced_theorem Comprehension sound "$comprehension_soundness"

  reject_roster_paths 'Comprehension or abstraction/instantiation execution owner path' \
    "$repo_root/VisualProof/Concrete" "$repo_root/VisualProof/Refinement"
  reject_roster_matches 'Comprehension or abstraction/instantiation execution declaration/import' \
    'comprehension|abstraction|instantiat' \
    "$repo_root/VisualProof/Concrete" "$repo_root/VisualProof/Refinement"
  reject_roster_matches 'Comprehension execution branch' 'comprehension' \
    "$rule_step" "$repo_root/VisualProof/Refinement/Step" \
    "$repo_root/VisualProof/Refinement/Step.lean" \
    "$repo_root/VisualProof/Refinement/Complete" \
    "$repo_root/VisualProof/Refinement/Complete.lean" \
    "$repo_root/VisualProof/Refinement/Means.lean"
  reject_roster_matches 'obsolete Proof request name' \
    'comprehension(Abstract|Instantiate)' "$repo_root/VisualProof/Proof"

  local means="$repo_root/VisualProof/Refinement/Means.lean"
  if [[ -f $means ]]; then
    assert_exact_roster 'Refinement.Means request constructor cases' "${concrete_expected[@]}" \
      < <(means_request_cases "$means")
    local default_case
    while IFS= read -r default_case; do
      [[ -n $default_case ]] || continue
      printf 'Refinement.Means wildcard/default request case: %s\n' "$default_case"
      violations=$((violations + 1))
    done < <(means_request_default_cases "$means")
  fi

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
