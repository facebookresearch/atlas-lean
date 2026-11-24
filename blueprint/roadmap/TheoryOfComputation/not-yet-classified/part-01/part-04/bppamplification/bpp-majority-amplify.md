# Bpp majority amplify

BPP error amplification (one-sided form, finite): independent
votes each equal to `true` with probability at least `2 / 3` under
a product law on tuples (weight of a tuple is the product of the
per-vote probabilities, here with a common bias lower bound given
through a single PMF `p` on `Bool` with `p true ≥ 2 / 3`): the
majority is wrong (`false`) with probability at most
`exp (-(n / 18))`. The tuple law is the product PMF
built by recursion on the tuple as a function `Fin n → Bool`
weighted by `∏ i, (p (v i)).toReal`.

The proof applies `mcdiarmid_product_general` to the number of `false`
votes: it has mean `n · P(false) ≤ n / 3`, a wrong majority puts it at
least `n / 2`, and one vote changes it by at most `1`, so the deviation
`n / 6` has weight at most `exp (-2 (n / 6) ^ 2 / n) = exp (-n / 18)`.
