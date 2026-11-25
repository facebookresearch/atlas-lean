# Delta Chain

Indexed face chain for the `P_δ` normal form.

`DeltaChain n m` represents a composite of `m - n` face maps `δ` from `mk n` to `mk m`. The
constructors store `Fin` indices and target degrees definitionally, eliminating internal `eqToHom`
and `Fin.ofNat`.

Insertion-sort normalization gives an admissible strictly increasing face chain.
