# Kleene source provenance

The Kleene simulation proof, its invariant-absorption corollary and the
three abstract sliding/zero/identity consumers were reused from the same
Meta program-verification development in `facebookresearch/atlas-lean`.
The original development was unpublished. Its recorded Git revision is
`8b3505eec6349259e3d6e0bb92d125cf54dcaaa0`; this record does **not** assume
that GitHub can resolve that historical revision.

Instead, the complete original files are preserved here as byte-identical,
in-tree plaintext snapshots, including their original Meta license headers:

- [`Algebra.lean.txt`](Algebra.lean.txt) preserves the original path
  `CSLibExt/Logics/PDL/Algebra.lean`. The reused declarations are
  `Cslib.PDL.Algebra.star_simulation` (lines 192-201) and
  `Cslib.PDL.Algebra.test_star_absorption` (lines 205-215).
- [`AlgebraTests.lean.txt`](AlgebraTests.lean.txt) preserves the original path
  `CSLibExtTest/Logics/PDL/AlgebraTests.lean`. The three reused consumers
  occupy lines 228-237. Other tests in this snapshot preserve source context;
  they are not additional tests or results compiled by this change.

[`manifest.json`](manifest.json) records the origin repository/revision,
paths, full-file SHA-256 and Git blob IDs, and declaration/span hashes.
The snapshots, rather than a dead commit link or a stylistic reference,
make the reused source directly inspectable from the published tree.

The production declarations keep exactly the original assumptions,
conclusions and proof bodies. Their surrounding namespace changed from
`Cslib.PDL.Algebra` to `KleeneAlgebra`; the abstract consumers changed only
those qualified theorem references. Module imports and documentation were
adapted to the general-mathematics location. Subsequent concrete consumer
examples are new tests, not attributed to this source.

The source's Kozen citation describes its mathematical style. It is not a
claim that these Lean proofs were transcribed from Kozen's paper. Original
Meta copyright and repository license apply to the preserved source.

These `.lean.txt` files are documentation assets, not Lean modules. They
must not be renamed to `.lean` or imported into a compiled library. They
preserve the source's PDL context without adding a compiled PDL dependency
or a duplicate proof stack.

To verify the full-file receipts locally:

```sh
cd docs/provenance/kleene
sha256sum Algebra.lean.txt AlgebraTests.lean.txt
```

Expected output:

```text
9527c27ba8da034c8c37f649eb74ba64283d89ad87e95f0f980a8a77306795ec  Algebra.lean.txt
9f8a2f416f1af884e2d5fb414b2a50bc6f4e39a845860db571bd8bf501f4b0f1  AlgebraTests.lean.txt
```
