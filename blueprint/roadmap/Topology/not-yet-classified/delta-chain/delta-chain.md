# Delta Chain

Indexed face chain for the `P_δ` normal form.

`DeltaChain n m` represents a composite of `m - n` face maps `δ`
from `mk n` to `mk m`. The constructors store `Fin` indices and target
degrees definitionally, eliminating internal `eqToHom` and `Fin.ofNat`.

The file also supplies native insertion-sort normalization to admissible
strictly increasing form; uniqueness and equivalence remain later results.
