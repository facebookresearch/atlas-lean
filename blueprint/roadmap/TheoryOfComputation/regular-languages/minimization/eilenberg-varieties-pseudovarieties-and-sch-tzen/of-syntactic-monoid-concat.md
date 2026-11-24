# Of syntactic Monoid concat

Aperiodicity of syntactic monoids is preserved under language concatenation. For a word
`x`, let `kL`, `kK` be the stabilization exponents of its classes in the two syntactic
monoids, and put `N = kL + kK + 1`. A split of `u * x ^ (N + 1) * v` in `L * K` either
cuts in `u` or `v`, where one side stabilizes by `N ≥ kL, kK`, or cuts inside the repeated
block, where the cut can be shifted by one copy: if the left part already contains more
than `kL` full copies, delete a copy on the left; otherwise the right part contains more
than `kK` full copies, so delete a copy on the right. The reverse direction inserts a
copy by the same case split. This is the syntactic form of the Schützenberger product
argument.

## Sources

- Schützenberger, "On finite monoids having only trivial subgroups", Information and Control 8 (1965), 190-194.
