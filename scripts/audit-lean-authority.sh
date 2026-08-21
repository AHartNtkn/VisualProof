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
  local expected=$'wireSever\niteration\ndoubleCut\nvacuity\npresentation\nidentification\ncutShape\nparallelShape\nends\narity\nargumentPermutation\nargumentDuplicate\nargumentProjection\nformalApplication\nidentityLeaf'
  local actual
  actual=$(awk '
    /^inductive Step\.Evidence / { inside = 1; next }
    inside && /^def Step / { exit }
    inside && $1 == "|" && $2 ~ /^[[:alpha:]][[:alnum:]_]*$/ { print $2 }
  ' "$step")

  if [[ $actual != "$expected" ]]; then
    printf 'Rule.Step roster mismatch\nexpected:\n%s\nactual:\n%s\n' \
      "$expected" "$actual" >&2
    return 1
  fi
  if rg -n '^  \|[[:space:]]*(comprehension|erasure)\b' "$step"; then
    printf 'Rule.Step contains forbidden constructor\n' >&2
    return 1
  fi
  printf 'roster: exact fifteen Rule.Step constructors\n'
}

audit_step_contract() {
  local contract_file axiom_output axiom_count unexpected_axiom
  contract_file=$(mktemp --suffix=.lean)
  trap 'rm -f "$contract_file"; trap - RETURN' RETURN

  cat >"$contract_file" <<'LEAN'
import VisualProof

namespace VisualProof.Rule

open Diagram
open Theory

example :
    ∀ {boundary : List Sig}
      {source source' target target' : OpenDiagram boundary},
      OpenDiagramIso source source' →
      Step source target →
      OpenDiagramIso target target' →
      Step source' target' :=
  @Step.iso

example :
    ∀ {boundary : List Sig}
      {source target : OpenDiagram boundary},
      Step source target →
      ∀ (model : VisualProof.Model) (args : Values model boundary),
        denoteOpen model source args → denoteOpen model target args :=
  @Step.sound

example :
    ∀ {boundary : List Sig}
      {source target : OpenDiagram boundary},
      Step source target →
      ∃ evidence : Step.Evidence source target,
        evidence.ForwardExecutable :=
  @Step.forward_execution_complete

example :
    ∀ {boundary : List Sig}
      {source target : OpenDiagram boundary},
      Step source target →
      ∃ evidence : Step.Evidence source target,
        evidence.BackwardExecutable :=
  @Step.backward_execution_complete

#print axioms Step.iso
#print axioms Step.sound
#print axioms Step.forward_execution_complete
#print axioms Step.backward_execution_complete

end VisualProof.Rule
LEAN

  if ! axiom_output=$(cd "$repo_root" && lake env lean "$contract_file" 2>&1); then
    printf '%s\n' "$axiom_output" >&2
    printf 'implementation: public Step contract does not elaborate\n' >&2
    return 1
  fi
  printf '%s\n' "$axiom_output"

  axiom_count=$(awk '/(depends on axioms:|does not depend on any axioms)/ { count++ } END { print count + 0 }' \
    <<<"$axiom_output")
  if [[ $axiom_count -ne 4 ]]; then
    printf 'implementation: expected four Step axiom reports, found %s\n' \
      "$axiom_count" >&2
    return 1
  fi
  if [[ $axiom_output == *sorryAx* ]]; then
    printf 'implementation: public Step contract depends on sorryAx\n' >&2
    return 1
  fi

  while IFS= read -r unexpected_axiom; do
    [[ -n $unexpected_axiom ]] || continue
    case "$unexpected_axiom" in
      propext|Classical.choice|Quot.sound) ;;
      *)
        printf 'implementation: public Step contract depends on project axiom: %s\n' \
          "$unexpected_axiom" >&2
        return 1
        ;;
    esac
  done < <(
    sed -n 's/.*depends on axioms: \[\(.*\)\]/\1/p' <<<"$axiom_output" |
      tr ',' '\n' |
      awk '{$1=$1; if (NF) print}' |
      sort -u
  )
}

audit_implementation() {
  local root="$repo_root/VisualProof/Rule/Executable"
  local umbrella="$repo_root/VisualProof/Rule/Executable.lean"
  local step_executor="$root/Step.lean"
  if [[ ! -d $root || ! -f $umbrella ]]; then
    printf 'implementation: executable authority is not installed yet\n' >&2
    return 1
  fi

  if ! audit_roster; then
    violations=$((violations + 1))
  fi

  if [[ ! -f $step_executor ]]; then
    printf 'missing Step execution coverage owner: %s\n' "$step_executor"
    violations=$((violations + 1))
  else
    local coverage_theorem
    for coverage_theorem in forward_execution_complete backward_execution_complete; do
      if ! rg -q "^theorem Step\\.$coverage_theorem\\b" "$step_executor"; then
        printf 'missing Step execution coverage theorem declaration: %s\n' \
          "$coverage_theorem"
        violations=$((violations + 1))
      fi
    done
  fi

  while IFS= read -r match; do
    [[ -n $match ]] || continue
    printf 'forbidden Comprehension execution reference: %s\n' "$match"
    violations=$((violations + 1))
  done < <(rg -n '\bComprehension\b' \
    "$root" "$umbrella" || true)

  if [[ -f $step_executor ]]; then
    while IFS= read -r match; do
      [[ -n $match ]] || continue
      printf 'forbidden independent Step execution roster: %s\n' "$match"
      violations=$((violations + 1))
    done < <(rg -n '^[[:space:]]*inductive[[:space:]]' "$step_executor" || true)
  fi

  while IFS= read -r match; do
    [[ -n $match ]] || continue
    printf 'forbidden aggregate Step executor or dispatcher: %s\n' "$match"
    violations=$((violations + 1))
  done < <(rg -n '^[[:space:]]*(noncomputable[[:space:]]+)?(def|abbrev|opaque)[[:space:]]+(Step\.)?(runForward|runBackward|run|execute|dispatch|dispatcher)\b' \
    "$step_executor" "$umbrella" || true)

  local match
  while IFS= read -r match; do
    [[ -n $match ]] || continue
    printf 'forbidden executable dependency: %s\n' "$match"
    violations=$((violations + 1))
  done < <(rg -n '^import VisualProof\.(Model|Diagram\.Semantics($|\.)|Rule\.Soundness($|\.)|Concrete($|\.)|Refinement($|\.)|Proof($|\.))' \
    "$root" "$umbrella" || true)

  local rule file declaration
  for rule in Erasure WireSever Iteration DoubleCut Vacuity Presentation Identification; do
    file="$root/$rule.lean"
    if [[ ! -f $file ]]; then
      printf 'missing executable rule module: %s\n' "$rule"
      violations=$((violations + 1))
      continue
    fi
    for declaration in ForwardIndex BackwardIndex runForward runBackward \
        forward_exact backward_exact; do
      if ! rg -q "^(abbrev|inductive|def|theorem) $declaration\\b" "$file"; then
        printf 'missing executable declaration: %s.%s\n' "$rule" "$declaration"
        violations=$((violations + 1))
      fi
    done

    local relation="$repo_root/VisualProof/Rule/$rule.lean"
    for declaration in respectsTargetIso backward_respectsTargetIso; do
      if ! rg -q "^theorem $rule\\.$declaration\\b" "$relation"; then
        printf 'missing relation closure theorem: %s.%s\n' \
          "$rule" "$declaration"
        violations=$((violations + 1))
      fi
    done
  done

  while IFS= read -r match; do
    [[ -n $match ]] || continue
    printf 'forbidden executable abstraction or limit override: %s\n' "$match"
    violations=$((violations + 1))
  done < <(rg -n '\b(Program|ExecutableFamily|Functional|Direction)\b|set_option (maxHeartbeats|maxRecDepth)' \
    "$root" "$umbrella" || true)

  if (( violations > 0 )); then
    printf 'implementation: %d violation(s)\n' "$violations" >&2
    return 1
  fi
  if ! (cd "$repo_root" && lake build VisualProof.Rule.Soundness VisualProof.Rule.Executable.Step); then
    printf 'implementation: public Step contract owners do not build\n' >&2
    return 1
  fi
  if ! audit_step_contract; then
    return 1
  fi
  if ! (cd "$repo_root" && lake env lean VisualProof/ComputabilityAudit.lean); then
    printf 'implementation: public runner compilation audit failed\n' >&2
    return 1
  fi
  printf 'implementation: clean boundary; Lean audited coverage and compiled 32 public runners (30 Step, 2 Erasure)\n'
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
