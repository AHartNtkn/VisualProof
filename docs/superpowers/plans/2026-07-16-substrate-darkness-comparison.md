# Substrate Darkness Comparison Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generate six controlled full-interface substrate-darkness options and a labeled contact sheet.

**Architecture:** A single review script reads the accepted render, applies six tonal transforms through one fixed rounded aperture mask, validates their luminance/contrast relationships, and writes review images. No production asset or application code changes.

**Tech Stack:** Python, Pillow.

## Global Constraints

- Only aperture pixels may change.
- All candidates retain the same indigo hue family and material texture.
- Surrounding interface pixels remain identical.
- Outputs are review evidence, not production selections.

---

### Task 1: Generate and validate the comparison

**Files:**
- Create: `scripts/build-substrate-darkness-options.py`
- Create: `review/interface-static/substrate-darkness/options-{a,b,c,d,e,f}.png`
- Create: `review/interface-static/substrate-darkness/comparison.png`
- Create: `review/interface-static/substrate-darkness/measurements.txt`

**Interfaces:**
- Consumes: `review/interface-static/cursebreaker-approved-desk.png`.
- Produces: six 1600×1000 full-interface renders and one labeled contact sheet.

- [x] **Step 1: Define the fixed aperture mask and six tonal transforms**
- [x] **Step 2: Generate all full-interface variants**
- [x] **Step 3: Validate unchanged exterior pixels and candidate relationships**
- [x] **Step 4: Assemble and inspect the labeled contact sheet**
