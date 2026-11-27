# Razborov's rank method: the middle slice is not in AC0[2]

No family of circuits with $\neg$, unbounded fan-in $\wedge,\vee$ and $\mathrm{MOD}_2$ gates of constant depth and polynomial size decides the middle slice $\mathrm{MS}$. Since $\mathrm{MS}\in\mathsf{P}$, this gives $\mathsf{P}\not\subseteq\mathsf{AC}^0[2]$ with an explicit witness.

## Proof sketch

By Smolensky's approximation a depth-$d$ circuit of size $s$ equals a polynomial of degree $\ell^d$ plus an error supported on at most $s2^n/2^\ell$ inputs. If $\ell^d+2a<n$ the polynomial has zero matrix, so $\operatorname{rank}Z_a\le s2^n/2^\ell$. The middle slice has $Z_a=I$ of full rank $\binom{n}{a}\ge\tfrac45 2^n/(n+1)$ at $a=a(n)$, which forces $s\ge 2^{\Omega(n^{1/(2d)})}$.

## Depends on

- [The middle slice function](the-middle-slice-function.md)
- [The class $\mathsf{AC}^0(m)$](../../../complexity-classes/time-and-space-complexity-classes/ac0-mod.md)

## Proof depends on

- [Razborov's GF(2) rank property of truth tables](razborov-gf2-rank-property.md)
- [Razborov–Smolensky polynomial approximation of AC0[p]](../razborovsmolensky-polynomial-approximation-of.md)

## Sources

- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR 41(4), 1987.
- Alexander A. Razborov, Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences 55(1), 1997 (Section 3.2).
- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
