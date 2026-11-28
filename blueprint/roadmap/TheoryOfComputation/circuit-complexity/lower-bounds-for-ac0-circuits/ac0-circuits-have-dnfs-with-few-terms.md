# AC0 circuits have DNFs with few terms

Every Boolean circuit of size $s$ and depth $d$ on $n$ inputs has an equivalent DNF with at most $\mathrm{poly}(n)\cdot s\cdot 2^{n(1-\mu)}$ terms, where $\mu\ge 1/O(\log(s/n)+d\log d)^{d-1}$, so a small constant-depth circuit splits the cube into noticeably fewer than $2^n$ regions.

For every Boolean circuit $C$ on $n$ inputs of size $s$ and depth $d$ there is a DNF formula equivalent to $C$ with at most

$$
\mathrm{poly}(n)\cdot s\cdot 2^{n(1-\mu)}\ \text{terms},\qquad\mu\ge\frac{1}{O(\log(s/n)+d\log d)^{d-1}}.
$$

The bound is below $2^n$ only while $\log s+O(\log n)<\mu n$, so it is non-trivial for circuits of size $s\le 2^{\varepsilon n^{1/d}}$, for a constant $\varepsilon=\varepsilon(d)>0$ and all large enough $n$.

## Expansion

The result is due to Impagliazzo, Matthews and Paturi. The known lower bounds for $\mathsf{AC}^0$ rest on the fact, made precise by the switching lemma, that almost all random restrictions simplify a small $\mathsf{AC}^0$ circuit to a function that depends on fewer than the remaining unrestricted variables. Made quantitative, this partitions $\{0,1\}^n$ into not too many disjoint subcubes on each of which the circuit is constant; the subcubes on which it equals $1$ are the terms of the DNF. The range $s\le 2^{O(n^{1/(d-1)})}$ in which Impagliazzo, Matthews and Paturi obtain non-trivial savings measures $\mu$ against the brute-force time $|C|\cdot 2^n$, which does not count the factor $s$; for the number of terms that factor counts, which shrinks the range to $s\le 2^{\varepsilon n^{1/d}}$.

## Depends on

- [The class $\mathsf{AC}^0$](../../complexity-classes/time-and-space-complexity-classes/ac0.md)

## Proof depends on

- [Impagliazzo–Matthews–Paturi extended switching lemma](impagliazzo-matthews-paturi-extended-switching-lemma.md)

## Sources

- Ruiwen Chen, Valentine Kabanets, Antonina Kolokolova, Ronen Shaltiel and David Zuckerman, "Mining Circuit Lower Bound Proofs for Meta-Algorithms", *Computational Complexity* 24, 2015, https://doi.org/10.1007/s00037-015-0100-0, read in the authors' copy of the journal edition <https://www.cs.mun.ca/~kol/papers/shrink-journal.pdf> (Lemma 3.1, stating the result of Impagliazzo, Matthews and Paturi without proof, and Section 3.2).
- Russell Impagliazzo, William Matthews and Ramamohan Paturi, "A Satisfiability Algorithm for AC0", *Proceedings of the Twenty-Third Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2012)*, pp. 961–972, https://doi.org/10.1137/1.9781611973099.77, read in arXiv:1107.3127v1 <https://arxiv.org/abs/1107.3127v1> (Theorem 1.2: for a circuit $C$ with $cn$ gates and depth $d$, a Las Vegas algorithm that partitions $\{0,1\}^n$ into restrictions on each of which $C$ is constant, in expected time and with expected number of restrictions $\mathrm{poly}(n)|C|2^{n(1-\mu)}$, with $\mu\ge 1/O(\log c+d\log d)^{d-1}$, proved in Section 3 from Lemma 1.4 and Corollary 1.5 of Section 3.2; item 2 after Theorem 1.3 for the savings range).
