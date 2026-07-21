# Headstrip Selection and Shared Context Menu Design

## Outcome

Headstrip must behave according to the selected proof objects, not the incidental
presence of the wire that visibly connects its two terms. The proof-action and
construction-edit context menus must also use one shared dark visual system based
on the existing proof-action menu.

## Headstrip Selection Semantics

A headstrip candidate consists of exactly two distinct term nodes. Selection may
also contain the unique output equation wire shared by those terms. That wire is
part of the same visible relationship and does not alter the requested proof move.

Any other selected object prevents headstrip recognition. This includes another
node, a region, an unrelated wire, or more than one wire. After selection is
normalized, the proof kernel remains authoritative: it must validate the exact
headstrip step before the controller offers or executes it.

Delete and Backspace use the same recognition path. Both therefore accept either
of these selections:

- the two valid term nodes; or
- the two valid term nodes plus their unique shared output wire.

## Shared Context Menu Styling

There will be one context-menu stylesheet and one semantic class family. Its
palette, typography, borders, shadows, headings, action rows, hover states, and
input treatment are shared by every right-click menu. The current proof-action
menu is the visual source: dark translucent navy, cyan borders and headings, light
text, and subtle blue action highlighting.

The proof-action menu and construction spawn cascade may retain only structural
differences required by their layouts, such as fixed positioning for the proof
menu and nested columns for the spawn cascade. Those structural rules live beside
the shared visual rules rather than in competing component palettes.

The construction menu's inline white, amber, and stone color declarations and
JavaScript hover-color mutations will be removed. The proof menu's private style
classes will likewise be migrated to the shared class family and removed, so a
second right-click-menu appearance cannot remain available.

## Validation

Focused controller tests will prove that both Delete and Backspace execute
headstrip with the shared wire selected, that the existing two-node selection
continues to work, and that an unrelated selected wire is rejected.

Focused browser tests will open both context-menu variants and compare their
computed palette-bearing styles. Source checks will confirm that the displaced
white construction palette and private proof-menu style classes are absent. The
relevant focused tests and the project typecheck will be run; the unrelated,
hours-long physics suite will not be run.
