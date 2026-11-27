# Code quality

Is the code readable, modular and cheap to maintain and build? This is the general
software-engineering rubric.

Check:

- **Size and decomposition**: proofs over about 60 lines that should be split into
  named lemmas; files over 1,250 lines; a declaration that mixes several results.
- **Repetition**: the same nontrivial argument appearing twice in the file (see
  `repeated_proof_machinery`); copy-pasted blocks differing by a constant.
- **Private helpers**: a public result resting on many `private` lemmas that other
  files would want; or, conversely, public helpers with no use outside one proof.
- **Imports**: wholesale `import Mathlib`; imports that are not needed; a module that
  many others import but that changes often (it invalidates the build cache).
- **Readability**: meaningful local names, comments on non-obvious steps, no dead
  code or commented-out proofs, no stray `#check`/`#eval`, no `set_option` without a
  documented reason.
- **Placement**: the declaration is in the right library and directory
  ([REVIEWING.md](../../REVIEWING.md#library-roles)), and not in a test or WantedExt
  file it does not belong to.

Anchors:

- 5: clear, well decomposed, nothing to tidy.
- 4: small tidy-ups.
- 3: a refactor would materially help (split a long proof, extract a shared lemma, narrow imports).
- 2: hard to read or to change; obvious duplication or misplacement.
- 1: unmaintainable.
