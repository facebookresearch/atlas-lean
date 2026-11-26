# Guruswami–Lyu–Wang: GV codes, list-decoding capacity and rigid matrices reduce to log-depth and NC0_4 Avoid

The explicit construction of binary linear codes achieving the Gilbert–Varshamov bound, of codes achieving list-decoding capacity, and of rigid matrices each reduce in polynomial time to the range avoidance problem for circuits of logarithmic depth, and, by a further reduction of Ren, Santhanam and Wang, to $\mathrm{NC}^0_4$-Avoid, in which every output bit depends on at most $4$ input bits.

## Proof sketch

For a linear code, a generator matrix with a nonzero codeword of low weight is described by the message and a sparse error pattern; the map from such descriptions to the parity-check or generator data is computable by low-depth circuits with stretch. The same holds for low-rank-plus-sparse decompositions of non-rigid matrices and for dense clusters violating list decodability. A log-depth circuit is then converted into an $\mathrm{NC}^0_4$ circuit with slightly larger stretch by adding the intermediate gate values as inputs.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)
- [Gilbert–Varshamov bound for linear codes](../../../../InformationTheory/error-correcting-codes/bounds-on-code-size/exists-linear-code-finrank-eq.md)
- [List-decoding capacity, achievability](../../../../InformationTheory/error-correcting-codes/list-decoding/exists-encoding-list-decodable.md)

## Proof depends on

- [Ren–Santhanam–Wang: Avoid for AC0 or NC0_4 with small stretch implies NC1 lower bounds](rsw-weak-class-avoid-implies-lower-bounds.md)
- [Probabilistic-method explicit constructions reduce to Avoid](explicit-constructions-in-apepp.md)

## Sources

- Venkatesan Guruswami, Xin Lyu and Xiuhan Wang, "Range Avoidance for Low-Depth Circuits and Connections to Pseudorandomness", APPROX/RANDOM (2022), ECCC TR22-102.
