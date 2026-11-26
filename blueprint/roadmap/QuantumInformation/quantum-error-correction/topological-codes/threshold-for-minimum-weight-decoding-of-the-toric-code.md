# Threshold for minimum-weight decoding of the toric code

Suppose each edge of the $L \times L$ [toric code](toric-code.md) suffers a bit flip independently with probability $p$,
and the syndrome is measured perfectly. If $p < 0.0373$, more precisely if $4\mu^2 p(1 - p) < 1$ where $\mu \approx 2.638$
is the connective constant of self-avoiding walks on the square lattice (at most $\mu^{\ell} e^{O(\sqrt{\ell})}$ of them
have length $\ell$), then the probability that
[minimum-weight decoding](minimum-weight-decoding-of-the-toric-code.md) fails is at most
$e^{o(L)} \cdot (4\mu^2 p(1 - p))^{L/2}$, and so tends to $0$ exponentially in $L$. With faulty syndrome
measurements, repeated over time with error probability $q$ per measurement, the same holds for $p, q < 0.0114$.

Dennis, Kitaev, Landahl and Preskill relate the threshold of the optimal decoder to a phase transition of the
random-bond Ising model and quote the numerical value $p_c \approx 0.1094$; that value is not a theorem.

## Depends on

- [Toric code](toric-code.md)
- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Proof depends on

- [The probability that a fixed cycle lies in the error plus the correction](probability-that-a-fixed-cycle-lies-in-the-error-plus-the-correction.md)
- [Minimum-weight decoding fails only on a homologically nontrivial cycle](minimum-weight-decoding-fails-only-on-a-nontrivial-cycle.md)
- [Counting self-avoiding walks on the square lattice](counting-self-avoiding-walks-on-the-square-lattice.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V, equations (46)–(67), and Section IV.F.
