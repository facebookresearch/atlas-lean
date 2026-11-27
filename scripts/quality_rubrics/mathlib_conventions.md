# Mathlib conventions

Would the statement pass Mathlib's conventions? ATLAS defers to Mathlib's design
decisions; see the [naming conventions](https://leanprover-community.github.io/contribute/naming.html),
[style guide](https://leanprover-community.github.io/contribute/style.html) and
[documentation guide](https://leanprover-community.github.io/contribute/doc.html).

Check:

- **Naming**: theorem names describe the statement (`foo_le_bar_of_baz`), use
  `lowerCamelCase` for defs and `UpperCamelCase` for types and structures, the
  conclusion first and hypotheses after `_of_`, no book numbering (`theorem_24_2`,
  `lemma_3_1`, `prop_A`) as the primary name, no `_aux`/`_helper` on public API.
- **Namespaces**: the declaration lives in the namespace of its head symbol so dot
  notation works; no top-level clutter; no reuse of a Mathlib namespace for
  unrelated content.
- **Binders**: implicit `{}` for arguments determined by others, instance arguments
  `[]` for classes, `(hx : ...)` hypotheses explicit; no unused variables; universe
  polymorphism with `Type*` where Mathlib uses it; argument order matching nearby
  Mathlib lemmas.
- **Statement shape**: `simp`-normal forms, `≤`/`<` instead of `≥`/`>`, `↑` coercions
  placed as Mathlib places them, `Set`/`Finset` used as Mathlib does, iff lemmas for
  characterisations, `@[simp]`/`@[ext]`/`@[gcongr]` attributes where appropriate and
  not where harmful.
- **Documentation**: every public definition and main theorem has a docstring that
  states the result in words (LaTeX welcome); the module has a header docstring.
- **theorem vs lemma**: follow the library's convention (PhyslibExt reserves
  `theorem` for well-known physics results).

Anchors:

- 5: indistinguishable from good Mathlib code.
- 4: one or two convention slips (an argument should be implicit; a docstring missing a hypothesis).
- 3: naming or namespace problems that hurt discoverability, or several binder issues.
- 2: book-numbered names, top-level clutter, or a shape that blocks dot notation and `simp`.
- 1: ignores conventions throughout.
