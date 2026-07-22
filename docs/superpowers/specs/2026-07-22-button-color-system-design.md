# Theme-Owned Button Color System

## Outcome

Every VisualProof button must remain immediately legible in Light (Manuscript) and Dark (Slate), visibly adopt the selected mode, and preserve the application's warm paper-and-graphite identity. Orange remains an intentional emphasis color for focus, selection, and primary actions rather than an arbitrary decoration.

The implementation must eliminate the current 1.16:1 dark-mode button contrast failure and prevent any button surface from retaining a light-mode foreground or background after a theme change.

## Current Failure

Button presentation currently has several independent owners:

- generic chrome buttons inherit their text color from a themed panel but retain a light-only translucent-white background;
- spawn and proof menus hard-code white backgrounds and light-only hover colors in TypeScript;
- relation-workspace controls define a separate partial palette;
- fixed-side and temporal controls rely on inherited colors rather than explicit semantic states.

In Dark (Slate), representative navigation, utility, and lifecycle controls render warm light text over an almost-light background at 1.16:1 contrast. Menus appended outside `#chrome` also bypass its `data-color-mode` selector, so changing the canvas theme cannot consistently reach them.

## Design

### One theme authority

`Theme` will own a `controls` palette alongside its existing canvas and interaction palettes. The palette will describe semantic roles rather than component names:

- default surface, foreground, border, hover surface, and active surface;
- primary surface, foreground, border, hover surface, and active surface;
- disabled surface, foreground, and border;
- focus ring;
- menu surface, menu hover surface, and readable muted text for hints and headings.

Light (Manuscript) will use warm paper surfaces, dark brown ink, warm neutral borders, and a deeper rust-orange primary treatment. Dark (Slate) will use graphite surfaces, warm cream foregrounds, slate borders, and an amber primary treatment. The modes will share semantic roles but not foreground/background values.

All enabled text-bearing role/state pairs must meet WCAG AA's 4.5:1 contrast threshold because the interface uses small text. Disabled text will remain intentionally subdued but must still reach 3:1 so it does not become illegible. Focus indicators and control boundaries must reach 3:1 against their adjacent surfaces.

### Theme publication

A single presentation function will publish the active theme's control palette as CSS custom properties on the document root. It will also publish the active color-mode identity there. Theme changes will call this function in the same transaction that updates the canvas backdrop.

The document root, rather than `#chrome`, is the publication boundary because spawn menus, proof menus, fixed-side workspaces, and relation workspaces can be mounted outside the chrome subtree. Every application control will therefore inherit the same active semantic values regardless of mount location. The current `#chrome[data-color-mode]` button-color path will be removed rather than retained as a fallback.

TypeScript remains the only palette-value authority. CSS consumes the published semantic variables; it does not duplicate light and dark literals in separate media-query or selector palettes. VisualProof continues to start in Light (Manuscript) and changes only through its explicit theme control. The current `prefers-color-scheme` control styling will be removed because it can contradict the application-selected canvas theme.

### Control roles and component migration

The global application button rule will provide the default semantic role so an unclassified button cannot silently fall back to user-agent colors or inherited panel colors. It will explicitly define foreground, background, border, hover, active, focus-visible, and disabled presentation.

Specialized controls will select one of a small set of semantic variants:

- primary controls use the primary role;
- proof and spawn menu rows use the menu role;
- icon-like temporal and close controls use the default role with component-owned geometry;
- fixed-side and relation-workspace controls keep their layout and shape but consume semantic colors;
- selected or pressed controls may add a semantic state indicator without replacing their readable foreground/background pair.

Component CSS continues to own geometry: padding, radius, typography, layout, and sizing. It may not own button foreground, background, border, hover, active, disabled, or focus colors.

Inline TypeScript styles may continue to position ephemeral menus and size dynamic elements. All inline color declarations and pointer-event color mutations will be deleted. CSS `:hover`, `:active`, `:focus-visible`, and `:disabled` rules will express those states from the theme variables.

The migration covers:

- compass navigation, lifecycle, library, and utility buttons;
- temporal undo and redo controls;
- fixed-side declaration controls;
- shell action and library buttons;
- proof-action menus and prompts;
- spawn menus, search fields, rows, metadata, and headings where those values affect button readability;
- relation-workspace actions, primary finalization, and empty-marker controls.

No alias, compatibility selector, local dark override, or inline light-only fallback will preserve the displaced color model.

## Data Flow

1. The shell selects a `Theme` from `THEMES`.
2. The theme presentation function sets the canvas/document backdrop, root color-mode marker, and semantic CSS variables from that exact `Theme` object.
3. All mounted controls inherit the variables from the document root.
4. CSS maps a control's semantic role and interaction state to those variables.
5. Changing the theme republishes the complete palette before the next rendered interaction.

This keeps canvas and DOM presentation synchronized while allowing CSS to remain responsible for browser-native control states.

## Failure Handling

`Theme.controls` is required by the TypeScript type, so an incomplete theme fails at compile time rather than degrading to inherited or user-agent colors. The presentation function will publish every required property without a per-property fallback. Tests will fail if a required semantic pair is missing, unparsable, or below its contrast threshold.

## Validation

Validation will directly prove both token-level and rendered behavior:

1. A unit test calculates relative luminance and contrast for every enabled default, hover, active, primary, primary-hover, and primary-active foreground/background pair in both themes. It also checks disabled readability and boundary/focus contrast.
2. Browser coverage opens representative controls from every mount boundary, records computed foreground/background/border values in Light, changes to Dark through the real theme control, and verifies both that values change and that rendered text contrast meets the required threshold.
3. Browser coverage exercises default, hover, focus-visible, active where reliably observable, primary, and disabled states rather than validating only static token names.
4. DOM inspection confirms that button elements do not carry inline foreground, background, border, hover, active, disabled, or focus colors after representative menus and workspaces are opened.
5. Repository inspection confirms the removed TypeScript menu color mutations and obsolete local button palettes are absent.
6. Type checking, relevant unit suites, and end-to-end tests must pass after the migration.

The decisive regression evidence is a fresh rendered audit showing that the original 1.16:1 Dark (Slate) controls now meet their required contrast and that Light and Dark resolve to visibly different semantic surfaces.

## Scope

This work changes control presentation and its validation only. It does not redesign the canvas palette, alter proof behavior, change component layout, introduce additional themes, or perform unrelated visual cleanup.
