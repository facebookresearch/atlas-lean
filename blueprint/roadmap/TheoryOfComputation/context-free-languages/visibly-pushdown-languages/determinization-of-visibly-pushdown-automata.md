# Determinization of visibly pushdown automata

For every [visibly pushdown automaton](visibly-pushdown-automata.md) $M$ over $\tilde\Sigma$ with $n$ states there is a deterministic VPA $M'$ over $\tilde\Sigma$ with
$L(M') = L(M)$, $O(2^{n^2})$ states and a stack alphabet of size $O(2^{n^2} \cdot |\Sigma_c|)$. The construction is a subset construction on
*summaries*, sets of pairs of states $(q, q')$ such that $M$ can go from $q$ to $q'$ on the well-matched segment read since the last pending
call; the push transitions are simulated at the matching return. Consequently the class of VPLs over $\tilde\Sigma$ is closed under
complementation, and VPLs are deterministic context-free languages. The bound is essentially tight: there are languages of nested
words accepted by nondeterministic automata with $O(s)$ states for which every deterministic automaton needs $2^{s^2}$ states.

## Depends on

- [Deterministic context-free language](../grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic-context-free.md)
- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)

## Sources

- R. Alur and P. Madhusudan, "Visibly pushdown languages", *Proceedings of the 36th ACM STOC*, 2004; full version of August 2005, whose numbering is cited, <https://www.cis.upenn.edu/~alur/Stoc04.pdf>: Section 2.2, Theorem 2 (determinization) with its proof and Corollary 1.
- R. Alur and P. Madhusudan, "Adding nesting structure to words", *Journal of the ACM* 56(3), 2009, author copy <https://www.cis.upenn.edu/~alur/Jacm09.pdf>: Theorem 3.3 (determinization) and Theorem 3.4 (succinctness of nondeterminism), and Section 5.1 (VPLs are deterministic context-free languages).
