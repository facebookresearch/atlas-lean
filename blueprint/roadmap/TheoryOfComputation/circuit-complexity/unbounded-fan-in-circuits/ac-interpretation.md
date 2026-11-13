# Ac Interpretation

The Boolean meaning of the `ACGate` basis, as in `gateValue`: a constant outputs its value,
negation flips its argument, `and k` and `or k` are the conjunction and the disjunction of their
`k` arguments (`true` and `false` when `k = 0`), and `mod m k` outputs `true` exactly when
`m ≠ 0` and the number of `true` arguments is divisible by `m`.
