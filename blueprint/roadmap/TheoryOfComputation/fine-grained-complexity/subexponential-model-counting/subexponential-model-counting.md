# Subexponential exact model counting for bounded-width CNF

For each width $k$ there is a deterministic algorithm that computes the exact number of satisfying assignments of every CNF whose clauses have at most $k$ literals in time $O\bigl(2^{A\,s(n)}(L+1)^{e}\bigr)$ and space $O((L+1)^{b})$, where $n$ is the number of variables, $L$ the encoded length, and

$$
s(n)=\frac{n\,(\log\log(n+16))^{2}}{\sqrt{\log(n+16)}}=o(n).
$$

## Proof sketch

Sparsify the formula (with a counting-preserving, disjoint version of the IPZ sparsification) into $2^{o(n)}$ formulas of bounded density, choosing the sparsification parameter as a function of $n$; count each of them with the tensor-contraction counter and recombine by rational interpolation, keeping all parameter schedules feasible so the total exponent is the interpolation scale $s(n)$.

## Depends on

- [The exponents s_k of k-SAT and #k-SAT](../sat-exponents-and-hypotheses/k-sat-exponents.md)
- [Counting satisfying assignments of a CNF formula](../../counting-complexity/counting-satisfiability-sat/count-sat-fun.md)

## Proof depends on

- [Model counting by tensor contraction in time 2^{O(m/√log n)}](tensor-contraction-model-counting.md)
- [Impagliazzo–Paturi–Zane sparsification lemma](../sparsification-lemma/impagliazzo-paturi-zane-sparsification-lemma.md)

## Sources

- OpenAI, "The Exponential Time Hypothesis is False", Manuscript, 2026, Proposition 6.4.
