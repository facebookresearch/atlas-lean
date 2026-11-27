# NP is closed under positive truth-table reductions

If $A\le^{p}_{ptt}B$ (a polynomial-time truth-table reduction whose Boolean combiner is monotone in the oracle answers) and $B\in\mathsf{NP}$, then $A\in\mathsf{NP}$.

## Proof sketch

The certificate lists one candidate witness per query; the verifier treats a query as answered 'yes' iff its listed witness is valid. Monotonicity makes underestimated answers harmless: the combiner accepts on the verified answers iff it accepts on the true answers for a suitable choice of witnesses.

Derived here (not stated in the cited sources): disjunctive and conjunctive truth-table reductions are positive (their combiners OR and AND are monotone), so $\mathsf{NP}$ is closed under both; since complementing both sets turns a conjunctive reduction into a disjunctive one and vice versa, $\mathsf{coNP}$ is closed under conjunctive and disjunctive truth-table reductions as well.

## Depends on

- [Polynomial-time truth-table, bounded and Turing reductions](../reducibilities-and-isomorphism/truth-table-reductions.md)
- [The complexity class NP](../../the-classes-p-np-and-conp/np.md)

## Proof depends on

- [The class coNP](../../the-classes-p-np-and-conp/co-np.md)

## Sources

- Richard E. Ladner, Nancy A. Lynch and Alan L. Selman, "A comparison of polynomial time reducibilities", Theoretical Computer Science 1(2), 1975.
- Christos H. Papadimitriou, "Computational Complexity", Addison-Wesley, 1994.
