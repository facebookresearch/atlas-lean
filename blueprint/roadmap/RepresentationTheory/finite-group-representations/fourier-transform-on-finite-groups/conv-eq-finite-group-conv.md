# Two conventions for convolution on a finite group agree

For complex-valued functions $P, Q$ on a finite group $G$, the convolution
$(P * Q)(s) = \sum_t P(s t^{-1})\, Q(t)$ used for random walks equals the [convolution written with the other convention](../../../GroupTheory/characters-of-finite-groups/convolution-on-finite-groups/conv.md),
$(P * Q)(x) = \sum_y P(y)\, Q(y^{-1} x)$: reindex by $t = y^{-1} s$.

So results for either convention apply to the other on complex values; for instance the [convolution theorem for one-dimensional characters](../../../GroupTheory/characters-of-finite-groups/convolution-on-finite-groups/char-pair-conv.md)
is the one-dimensional case of [the Fourier transform turns convolution into composition](fourier-conv.md).

## Sources

- P. Diaconis and M. Shahshahani, *Generating a random permutation with random transpositions*,
  Z. Wahrsch. Verw. Gebiete 57 (1981), Section 2 (convolution $\sum_\eta P(\gamma\eta^{-1}) Q(\eta)$).
