# Threshold for minimum-weight decoding of the toric code

Suppose each edge of the $L \times L$ [toric code](toric-code.md) suffers a bit flip independently with probability $p$,
and the syndrome is measured perfectly. If $p < 0.0373$, more precisely if $4\mu^2 p(1 - p) < 1$ where $\mu \approx 2.638$
is the growth constant of self-avoiding closed walks on the square lattice (at most a polynomial in $\ell$ times $\mu^{\ell}$
of them have length $\ell$), then the probability that
[minimum-weight decoding](minimum-weight-decoding-of-the-toric-code.md) fails is at most
$Q(L) \cdot (4\mu^2 p(1 - p))^{L/2}$ for a polynomial $Q$, and so tends to $0$ exponentially in $L$. With faulty syndrome
measurements, repeated over time with error probability $q$ per measurement, the same holds for $p, q < 0.0114$.

Dennis, Kitaev, Landahl and Preskill relate the threshold of the optimal decoder to a phase transition of the
random-bond Ising model and quote the numerical value $p_c \approx 0.1094$; that value is not a theorem.

## Expansion

A good expansion adds pages for the two steps of the proof: the bound on the probability that a given closed path of
length $\ell$ lies in $e + e'$ (Section V.B: at least half of its edges carry errors, giving $(4p(1 - p))^{\ell/2}$ up to
counting), and the count of self-avoiding closed walks of length $\ell$ on the square lattice, at most a polynomial times
$\mu^{\ell}$, together with the fact that a failure needs a homologically nontrivial path of length at least $L$.

## Depends on

- [Toric code](toric-code.md)
- [Minimum-weight decoding of the toric code](minimum-weight-decoding-of-the-toric-code.md)

## Sources

- E. Dennis, A. Kitaev, A. Landahl and J. Preskill, *Topological quantum memory*, J. Math. Phys. 43 (2002), 4452–4505, arXiv:quant-ph/0110143, Section V, equations (46)–(67), and Section IV.F.
