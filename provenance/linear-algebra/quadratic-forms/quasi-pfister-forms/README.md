# Quasi-Pfister source provenance

The six original MathlibExt files come from
[fairinternal/formal-math, commit 50aea3f906434219750e084a5e88ecf073ede59c](https://github.com/fairinternal/formal-math/tree/50aea3f906434219750e084a5e88ecf073ede59c/MathlibExt/LinearAlgebra/QuadraticForm).
`originals.jsonl` retains their complete UTF-8 source texts and author notices.
Its bytes are unchanged from the original archive attached to PR #11042.
`manifest.json` records the exact upstream blobs and SHA256 values.

`files.jsonl` binds this revision's source and concrete client to their current
SHA256 values and records each adaptation. `Isometry.lean` contains helpers
extracted from the original `HalfDimensionalTotallyIsotropic.lean`; it is
recorded as an extraction rather than a seventh upstream original.

The subset-sum construction is a diagonal quasi-Pfister form over arbitrary
fields. It agrees with the quadratic Pfister form in characteristic different
from two and is totally singular in characteristic two. The roundness source
is Elman–Karpenko–Merkurjev, *The Algebraic and Geometric Theory of Quadratic
Forms*, Corollary 10.3; Corollary 9.9 covers the characteristic-different-from-two
Pfister case. The concrete client covers both the rational and `ZMod 2` forms.

The existing `pfisterLowerPart` and `pfisterSuccIndexEquiv` DATA definitions are
public APIs with unchanged constructor and proof bodies. All 39 previous public
declarations remain; the revised source has 41 public declarations in total.

The concrete client retains its rational declarations and all characteristic-two
claims. Its polar-form proof uses explicit vector binders, and its radical proof
applies the membership lemma with the coefficient field specified.
