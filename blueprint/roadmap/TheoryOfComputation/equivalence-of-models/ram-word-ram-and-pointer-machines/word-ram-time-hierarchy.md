# A time hierarchy for the word RAM

Fix a constant $k\ge1$ and consider word sizes $w$ with $k\log n\le w\le n^{k}$. There is a constant $d$ depending only on $k$ such that for every time-constructible, polynomially bounded $T$ with $T(n)\ge n$ some problem is decided by one fixed word-RAM program over the additive basis within $O(T(n)^{d})$ instructions at every such word size, but by no word-RAM program within $O(T(n))$ instructions at any such family of word sizes $w(n)$ that a multi-tape Turing machine computes from $n$ in time $O(T(n))$. (Some upper bound on $w$ is needed: with unit-cost multiplication on unboundedly long words, a RAM can build numbers with $2^{t}$ bits in $t$ steps. The uniformity of $w(n)$ is needed for the reduction to Turing machines: an arbitrary family of word sizes can encode nonuniform advice, which the Turing-machine simulation cannot reproduce.) That is, $\mathsf{RAMTIME}(T)\subsetneq\mathsf{RAMTIME}(T^{d})$.

## Proof sketch

Translate to multi-tape machines: word-RAM time $T$ at word size $w\le n^{k}$ is within Turing time $T^{c}$ for a constant $c=c(k)$ (using $T\ge n$, and computing $w(n)$ first in time $O(T(n))$), apply the deterministic time hierarchy theorem there to separate $\mathrm{DTIME}(T^{c})$ from $\mathrm{DTIME}(T^{c+1})$, and simulate the separating machine back on the word RAM with linear overhead. The repository's time-hierarchy node covers only linear versus quadratic time; the general case is the Hartmanis–Stearns theorem.

## Depends on

- [The word-RAM model](../../fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Polynomial time on the word RAM equals polynomial time on multi-tape Turing machines](word-ram-turing-polynomial-invariance.md)
- [Deterministic time hierarchy: quadratic versus linear time](../../hierarchy-theorems-and-barriers/time-hierarchy-theorem/time-hierarchy.md)

## Sources

- J. Hartmanis and R. E. Stearns, "On the Computational Complexity of Algorithms", Transactions of the American Mathematical Society 117, 285–306, 1965.
- Stephen A. Cook and Robert A. Reckhow, "Time Bounded Random Access Machines", Journal of Computer and System Sciences 7(4), 1973.
