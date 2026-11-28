# Equivalence of erasing pattern languages with regular constraints is undecidable

No algorithm decides whether two patterns with regular constraints on their variables generate the same erasing pattern language, over any
alphabet with at least two letters, even for patterns without letters.

**Theorem (Nowotka and Wiedenhöft).** For every alphabet $\Sigma$ with $|\Sigma| \ge 2$, it is undecidable, given [patterns with regular constraints](pattern-languages-with-regular-constraints.md)
$(\alpha, r_\alpha)$ and $(\beta, r_\beta)$ over $\Sigma$, whether $L_E(\alpha, r_\alpha) = L_E(\beta, r_\beta)$. This remains undecidable when $\alpha$ and $\beta$ are terminal-free.

For erasing pattern languages without constraints, decidability of equivalence is a long-standing open problem; for non-erasing pattern languages without
constraints equivalence is trivially decidable (Angluin).

## Depends on

- [Pattern languages with regular constraints](pattern-languages-with-regular-constraints.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof adapts the reduction of Freydenberger and Reidenbach for the inclusion problem over finite alphabets. It reduces the question whether a
nondeterministic two-counter automaton without input has an accepting computation, encoding a configuration $(q_i, m_1, m_2)$ as $0^{1+i} \# 0^{5+2m_1} \# 0^{5+2m_2}$ and
a computation as the concatenation of its configurations separated by $\#\#$. For the binary alphabet $\{0, \#\}$ it builds terminal-free constrained patterns
$\alpha$ and $\beta$ such that $L_E(\alpha, r_\alpha) \subseteq L_E(\beta, r_\beta)$ always fails at most on words $v 0 u 0 v$ in which $u$ encodes an accepting computation, while the reverse inclusion
always holds; so the two languages are equal exactly when the automaton has no accepting computation. Larger alphabets reduce to the binary case by restricting
the constraint languages to two letters.

## Sources

- D. Nowotka and M. Wiedenhöft, "The equivalence problem of E-pattern languages with regular constraints is undecidable", *Theoretical Computer Science* 1083, article 116126, 2026, doi:10.1016/j.tcs.2026.116126; conference version in *Implementation and Application of Automata (CIAA 2024)*, Lecture Notes in Computer Science, pp. 276–288, Springer, 2024, doi:10.1007/978-3-031-71112-1_20. Read in arXiv:2411.07275v1: Theorem 4 of Section 3 with its proof (Lemmas 5–7 and Corollary 8), Corollary 9 (terminal-free patterns) in Section 4, and the two-counter automata of Section 2.1, with the numbering of that version.
