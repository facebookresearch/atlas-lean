# Razborov's GF(2) rank property of truth tables

Let $h:\{0,1\}^n\to\mathbb{F}_2$ and $0\le a\le n$. The *zero-sum matrix* $Z_a(h)$ has rows and columns indexed by the $a$-element subsets of $\{1,\dots,n\}$, and its $(I,J)$ entry is the coefficient of the monomial $\prod_{i\notin I\cup J}x_i$ in the multilinear $\mathbb{F}_2$-polynomial representing $h$; equivalently

$$
Z_a(h)_{I,J}=\sum_{x:\ x_i=0\ \forall i\in I\cup J}h(x)\pmod 2 .
$$

The *rank property* (rank test) at level $a$ accepts $f$ iff $\operatorname{rank}_{\mathbb{F}_2}Z_a(f)\ge\tfrac12\binom{n}{a}$. Key facts: if $\deg h+2a<n$ then $Z_a(h)=0$; if $h$ is supported on a set $E$ then $\operatorname{rank}Z_a(h)\le|E|$; and the indicator of the inputs with exactly $a$ zeros has $Z_a$ equal to the identity matrix.

## Depends on

- [The middle slice function](the-middle-slice-function.md)
- [Natural property](../../../hierarchy-theorems-and-barriers/natural-proofs-barrier/natural-property.md)

## Sources

- Alexander A. Razborov, Steven Rudich, "Natural Proofs", Journal of Computer and System Sciences 55(1), 1997 (Section 3.2: Razborov's argument as a GF(2)-linear map to matrices with a large-rank test).
- Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets, Antonina Kolokolova, "Learning Algorithms from Natural Proofs", 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 2016.
- Alexander A. Razborov, "Lower Bounds on the Size of Bounded Depth Circuits over a Complete Basis with Logical Addition", Mathematical Notes of the Academy of Sciences of the USSR 41(4), 1987.
