# Polynomial-time uniform generator of gate approximants

This node collects the uniform, efficient generation of exactly unitary gate approximants used by the encoded
circuit model.

## Expansion

A sound expansion has separate pages for:

1. **Input and output.** An encoded target gate (for example a phase $e^{2\pi i/2^k}$, a Hadamard gate or a controlled
   phase), a rational accuracy $\varepsilon > 0$, and as output an exactly unitary matrix with Gaussian-rational
   entries within $\varepsilon$ of the target in operator norm.
2. **Efficiency.** The generator runs in time polynomial in the encoding length of the target and in
   $\log(1/\varepsilon)$, counting bit operations, and its output has bit-length polynomial in the same quantities.
3. **Certificate.** The output carries a checkable certificate of exact unitarity and of the accuracy bound.
4. **Use in circuit generators.** For the Hadamard gate and the controlled phases $\mathrm{diag}(1, 1, 1, e^{2\pi i/2^k})$, a
   polynomial-time circuit generator that calls the generator for $k \le n$ and accuracy $\delta$ divided by its number of
   gates, on circuits with polynomially many gates, remains polynomial-time computable.

The cited lecture notes are background for why such approximants are needed; this construction is
representation-specific and needs its own derivation or source.

## Depends on

- [Encoded 2-local quantum gate](../../complexity-classes/time-and-space-complexity-classes/qgate.md)
- [Well-formed quantum gate](../../complexity-classes/time-and-space-complexity-classes/qgate-well-formed.md)
- [Polynomial-time computable functions](../../complexity-classes/the-classes-p-np-and-conp/is-poly-time.md)

## Proof depends on

- [Snapping approximate values to exact Gaussian-rational unitaries](snapping-approximate-values-to-exact-gaussian-rational-unita.md)
- [Certified rational approximation of cos/sin(2 pi / 2^k) and 1/sqrt 2](certified-rational-approximation-of-cos-sin-and-1-sqrt-2.md)

## Sources

- R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415v6, §2.2 (approximate universality of gate sets; background, not a statement of this construction). <https://arxiv.org/pdf/1907.09415v6>
