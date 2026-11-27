# Compression of truth tables of small formulas, AC0 circuits and read-once branching programs

Given the truth table of a function computed by a small AC0 circuit, formula or read-once branching program, a deterministic $\mathrm{poly}(2^n)$-time algorithm finds some circuit for it noticeably smaller than the generic $2^n/n$ bound, at the sizes where lower bounds for these classes are known.

The compression problem for a circuit class $\mathcal{C}$: given the truth table of an $n$-variate Boolean function $f$ computable by a small $\mathcal{C}$-circuit, find in deterministic time $\mathrm{poly}(2^n)$ a circuit of any type computing $f$ whose size is less than the trivial bound $2^n/n$. Then:

1. ($\mathsf{AC}^0$.) There is a deterministic $\mathrm{poly}(2^n)$-time algorithm that, given the truth table of $f$ computable by an $\mathsf{AC}^0$ circuit of depth $d$ and size $s$, together with $d$ and $s$, outputs a DNF for $f$ with at most $\mathrm{poly}(n)\cdot s\cdot 2^{n(1-\mu)}$ terms, where $\mu\ge 1/O(\log(s/n)+d\log d)^{d-1}$. This is non-trivial up to size $2^{n^{1/(d-1)}}$.
2. (Formulas and branching programs.) There is an efficient algorithm that, given the truth table of a formula or branching program $F$ on $n$ variables with $L(F)\le n^d$, outputs an equivalent circuit of size at most $2^{n-n^{\varepsilon}}$ for some constant $0<\varepsilon<1$ depending on $d$, where $d<2.5$ for de Morgan formulas and $d<2$ for complete-basis formulas and branching programs.
3. (Read-once branching programs.) There is a deterministic $\mathrm{poly}(2^n)$-time algorithm that, given the truth table of $f$ computable by a read-once branching program of size $s$, outputs a formula for $f$ of size $O(sn^3\cdot 2^{n/2})$; for $s\le 2^{0.48n}$ this is below $2^{0.99n}$.

## Expansion

Each item extracts structure from the random-restriction proof of the corresponding lower bound and finds the structure greedily. For $\mathsf{AC}^0$, the switching lemma gives a DNF with few terms, and the greedy Set-Cover algorithm over all $3^n$ restriction terms finds a DNF at most $n$ times larger. For formulas, high-probability shrinkage gives a decision tree whose leaves are mostly sublinear-size subformulas; a generalized Set-Cover heuristic for functions of the form $C_1\vee\dots\vee C_\ell\vee C_{\ell+1}$, with small $C_1,\dots,C_\ell$ and $C_{\ell+1}$ accepting few inputs, recovers a small circuit. For read-once branching programs, the nodes at depth $n-k$ split the function into at most $3sn$ pairs of functions on disjoint variable sets. Such compression algorithms are a special kind of [natural property](../../hierarchy-theorems-and-barriers/natural-proofs-barrier/natural-property.md) in the sense of Razborov and Rudich.

## Depends on

- [Circuit complexity of a Boolean function and truth tables](../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)

## Proof depends on

- [AC0 circuits have DNFs with few terms](../lower-bounds-for-ac0-circuits/ac0-circuits-have-dnfs-with-few-terms.md)
- [High-probability shrinkage of formulas under greedy random restrictions](high-probability-shrinkage-under-greedy-restrictions.md)

## Sources

- Ruiwen Chen, Valentine Kabanets, Antonina Kolokolova, Ronen Shaltiel and David Zuckerman, "Mining Circuit Lower Bound Proofs for Meta-Algorithms", *Computational Complexity* 24, 2015, https://doi.org/10.1007/s00037-015-0100-0 (Compression Theorem in Section 1, Lemma 3.1, Theorems 3.2, 3.5, 3.6 and 3.8, Lemma 3.7).
