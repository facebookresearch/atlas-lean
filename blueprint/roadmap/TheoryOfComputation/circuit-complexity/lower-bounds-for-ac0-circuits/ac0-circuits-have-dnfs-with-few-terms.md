# AC0 circuits have DNFs with few terms

Every Boolean circuit of size $s$ and depth $d$ on $n$ inputs has an equivalent DNF with at most $\mathrm{poly}(n)\cdot s\cdot 2^{n(1-\mu)}$ terms, where $\mu\ge 1/O(\log(s/n)+d\log d)^{d-1}$, so a small constant-depth circuit splits the cube into noticeably fewer than $2^n$ regions.

For every Boolean circuit $C$ on $n$ inputs of size $s$ and depth $d$ there is a DNF formula equivalent to $C$ with at most

$$
\mathrm{poly}(n)\cdot s\cdot 2^{n(1-\mu)}\ \text{terms},\qquad\mu\ge\frac{1}{O(\log(s/n)+d\log d)^{d-1}}.
$$

The bound is below $2^n$, and so non-trivial, for circuits of size up to $2^{n^{1/(d-1)}}$, the size up to which lower bounds against $\mathsf{AC}^0$ are known.

## Expansion

The result is due to Impagliazzo, Matthews and Paturi. The known lower bounds for $\mathsf{AC}^0$ rest on the fact, made precise by the switching lemma, that almost all random restrictions simplify a small $\mathsf{AC}^0$ circuit to a function that depends on fewer than the remaining unrestricted variables. Made quantitative, this partitions $\{0,1\}^n$ into not too many disjoint subcubes on each of which the circuit is constant; the subcubes on which it equals $1$ are the terms of the DNF.

## Depends on

- [The class $\mathsf{AC}^0$](../../complexity-classes/time-and-space-complexity-classes/ac0.md)

## Proof depends on

- [Håstad's switching lemma](hastad-s-switching-lemma.md)

## Sources

- Ruiwen Chen, Valentine Kabanets, Antonina Kolokolova, Ronen Shaltiel and David Zuckerman, "Mining Circuit Lower Bound Proofs for Meta-Algorithms", *Computational Complexity* 24, 2015, https://doi.org/10.1007/s00037-015-0100-0 (Lemma 3.1, stating the result of Impagliazzo, Matthews and Paturi, and Section 3.2).
