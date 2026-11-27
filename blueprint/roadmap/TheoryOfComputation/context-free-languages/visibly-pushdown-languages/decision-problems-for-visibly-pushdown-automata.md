# Universality and inclusion for visibly pushdown automata are EXPTIME-complete

For [visibly pushdown automata](visibly-pushdown-automata.md), emptiness is decidable in polynomial time in the size of the automaton, as for any pushdown
automaton (for nested word automata in time $O(|A|^3)$ in the size of $A$), while the universality problem ($L(M) = \Sigma^*$?) and the inclusion problem ($L(M_1) \subseteq L(M_2)$?, for automata over a common pushdown alphabet) are complete for deterministic
exponential time ([EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)). Both are undecidable for general pushdown automata. Inclusion reduces to emptiness
of $L(M_1)$ intersected with the complement of $L(M_2)$; hardness of universality is by a reduction from the membership problem of
alternating linear-space Turing machines. For program verification the cost is polynomial in the program and exponential only in
the specification.

## Depends on

- [Visibly pushdown automata and visibly pushdown languages](visibly-pushdown-automata.md)
- [The class EXP](../../complexity-classes/time-and-space-complexity-classes/exp.md)

## Proof depends on

- [Closure properties of visibly pushdown languages](closure-properties-of-visibly-pushdown-languages.md)

## Sources

- R. Alur and P. Madhusudan, "Visibly pushdown languages", *Proceedings of the 36th ACM STOC*, 2004; full version of August 2005, whose numbering is cited, <https://www.cis.upenn.edu/~alur/Stoc04.pdf>: Section 2.3, the paragraph on emptiness, Theorem 3 with its proof, and Figure 2 (summary of decision problems).
