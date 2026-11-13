# Braid word for the Conway knot

The braid word
$\sigma_1^{-2} \sigma_2 \sigma_1^{-1} \sigma_2 \sigma_1^{-1} \sigma_3 \sigma_2^{-2} \sigma_3^{2}$
on $4$ strands, encoded as the list of integers $[-1, -1, 2, -1, 2, -1, 3, -2, -2, 3, 3]$, where
an entry $i > 0$ stands for the generator $\sigma_i$ and $-i$ for $\sigma_i^{-1}$. It has
length $11$ and writhe $-1$, and is a braid word for the Conway knot 11n34.

## Sources

- KnotInfo's `11n_34` record, `braid_notation` field. The Knot Atlas records a different but Markov-equivalent presentation for the same knot, `[1, 1, 2, -3, 2, 1, -3, -2, -2, -3, -3]` (which it labels `K11n34`, the mirror of the Conway knot); both representations agree on braid index 4, braid length 11, and writhe `-1`. Sliceness is mirror-invariant, so either braid word is a valid witness for `conway_knot_not_smoothly_slice`.
