# Near-maximum circuit lower bound for exponential time with a prMA oracle

Exponential time with smart queries to a promise-MA oracle and one bit of advice contains a function that requires circuits of size $2^n/n$, a near-maximum bound far beyond the half-exponential bounds known before for Merlin–Arthur-type classes.

With $\mathsf{prMA}$ and smart oracle access as defined for the smart $\mathsf{prMA}$ range-avoidance algorithm, let $\mathsf{smart}\text{-}\mathsf{E}^{\mathsf{prMA}}/1$ be the class of languages decided in time $2^{O(n)}$ by a deterministic oracle machine with one advice bit that, under the correct advice, queries a $\mathsf{prMA}$ oracle only on strings satisfying its promise. Then:

1. $\mathsf{smart}\text{-}\mathsf{E}^{\mathsf{prMA}}/1\not\subseteq\mathrm{SIZE}[2^n/n]$; in particular some function in $\mathsf{E}^{\mathsf{prMA}}/1$ requires circuits of size $\Omega(2^n/n)$.
2. For constants $\delta_1,\delta_2>0$ with $\delta_1+2\delta_2<1$, some $L\in\mathsf{smart}\text{-}\mathsf{E}^{\mathsf{prMA}}/1$ cannot be $(1/2+2^{-\delta_2 n})$-approximated by circuits of size $2^{\delta_1 n}$.
3. For every constant $k\ge 1$ and nice function $\alpha(n)\ge\omega(1)$, $\mathsf{smart}\text{-}\mathsf{E}^{\mathsf{prMA}}/1\not\subseteq\mathsf{TIME}[2^{kn}]/_{2^n-\alpha(n)}$.

By contrast, for a nice $f$ with $f(f(n^c)^c)=2^{o(n)}$ for every constant $c\ge 1$, the bound $\mathsf{E}^{\mathsf{prMA}}\not\subseteq\mathrm{SIZE}[f(n)]$ has a relativizing proof from the Karp–Lipton-type collapse of Chakaravarthy and Roy, but that argument stops at half-exponential size.

## Expansion

Run the smart $\mathsf{FP}^{\mathsf{prMA}}/1$ range-avoidance algorithm on the truth-table generator that maps an $n$-bit description of a circuit on $k+1$ inputs ($n=2^k$) to its $2n$-bit truth table. On infinitely many $k$ it outputs a truth table of length $2^{k+1}$ with no circuit of size $0.1\cdot 2^k/k$. Computing that truth table in time $2^{O(n)}$ and reading off the requested bit decides a language with the claimed hardness; since the algorithm is smart, the language is well defined regardless of out-of-promise oracle answers. Items 2 and 3 follow from direct reductions of these hardness conditions to range avoidance. The method extends the iterative win-win paradigm introduced for the [polynomial-time pseudodeterministic construction of primes](../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/pseudodeterministic-algorithms/polynomial-time-pseudodeterministic-primes.md).

## Depends on

- [Circuit complexity of a Boolean function and truth tables](../minimum-circuit-size-problem/circuit-complexity-of-a-boolean-function.md)
- [The class MA (Merlin–Arthur)](../../complexity-classes/time-and-space-complexity-classes/ma.md)
- [Smart prMA algorithm with one advice bit for range avoidance](smart-prma-algorithm-for-range-avoidance.md)

## Proof depends on

- [Korten: solving Avoid yields hard truth tables](../range-avoidance-and-near-maximum-lower-bounds/korten-avoid-to-hard-truth-table.md)

## Sources

- Hanlin Ren and Ryan Williams, "Near-Maximum Circuit Lower Bounds for Exponential Time with Merlin-Arthur Queries", *IEEE Symposium on Foundations of Computer Science (FOCS)*, 2026, arXiv:2607.09963v1 (Theorem 1.1, Theorem 4.5, Corollary 4.6, Theorem A.1).
