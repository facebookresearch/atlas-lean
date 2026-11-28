# Straight-line replaceAll with regular patterns is in EXPSPACE

When every pattern of replaceAll is a constant regular expression, while subjects and replacements may be variables, satisfiability of straight-line replaceAll constraints with regular-expression memberships is decidable in exponential space.

Consider the class $\mathrm{SL}[\mathrm{replaceAll}]$ of [straight-line replaceAll constraints](straight-line-replaceall-constraints.md) under the [leftmost-longest replaceAll](leftmost-longest-replaceall.md) semantics, over a finite alphabet given with the input, restricted to the *regular-expression case*: every pattern is a regular expression, subjects and replacements are variables or constant words, and the regular constraint is a conjunction of memberships $x \in e$ with regular expressions $e$. Satisfiability in this case is decidable in [EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md).

This page states only the upper bound. A matching lower bound is known for a different input representation: when regular constraints are given by finite automata, the single-letter case is already EXPSPACE-hard (Chen, Hague, Lin, Rümmer and Wu, 2019, Proposition 5.5, recorded with the [EXPSPACE fragments with replaceAll, reverse and transducers](expspace-fragments-with-replaceall-reverse-and-transducers.md)). That reduction uses polynomial-size automata, not regular expressions, and an alphabet that grows with the input; whether the regular-expression case with regular-expression memberships is EXPSPACE-hard is not settled by it.

## Depends on

- [Straight-line replaceAll constraints](straight-line-replaceall-constraints.md)
- [The class EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)

## Proof depends on

- [Emptiness of NFAs is decidable](../encoded-finite-automata/tm2-decidable-language-eq-zero.md)
- [Savitch's theorem](../../complexity-classes/savitch.md)

## Expansion

This node still needs its proof broken down; the source proof (Chen et al. 2018, Sections 5–8) has these parts. Normalize to a replaceAll-only formula by Proposition 3.6 (which is itself a proof step to be stated as its own result when expanded) and translate the regular expressions to automata in linear time. Repeatedly pick a conjunct $x = \mathrm{replaceAll}(y, e, z)$ whose output $x$ is used by no other conjunct, and replace the regular constraints on $x$ by regular constraints on $y$ and $z$ defining the pre-image: for a single-letter pattern $a$ and an automaton $A$ on $x$, guess a set $T_z$ of pairs of states of $A$; constrain $z$ by the intersection of the languages from $q$ to $q'$ for $(q, q') \in T_z$, and $y$ by the automaton $B_{A, a, T_z}$ obtained from $A$ by deleting its $a$-transitions and adding $a$-transitions $q \to q'$ for $(q, q') \in T_z$ (Section 6.1, Proposition 6.1). Constant-string patterns use a parsing automaton tracking window profiles of the leftmost matches (Section 7, Definitions 7.1 and 7.4); regular-expression patterns use an automaton tracking leftmost-longest matches (Section 8), with patterns matching only $\varepsilon$ treated separately and patterns matching both $\varepsilon$ and nonempty words handled by an extension the source only sketches, an obligation for the expansion. When no replaceAll remains, the regular constraints on source variables are tested for nonempty intersection. Complexity (Proposition 6.4 and Appendices D–E): the number of constraints collected on a variable is at most exponential, bounded through the number of paths in the dependency graph, and each automaton has exponentially many states; the guesses and the final nonemptiness test of the product, performed on the fly, use exponential space, and Savitch's theorem removes the nondeterminism.

## Sources

- T. Chen, Y. Chen, M. Hague, A. W. Lin and Z. Wu, "What is decidable about string constraints with the ReplaceAll function", Proceedings of the ACM on Programming Languages 2 (POPL), Article 3, 2018, doi:[10.1145/3158091](https://doi.org/10.1145/3158091); full version arXiv:1711.03363v1, <https://arxiv.org/abs/1711.03363v1>: Theorem 4.2, Section 5 (outline), Sections 6–8 (Proposition 6.1, Proposition 6.4, Definitions 7.1 and 7.4), and Appendices B, D and E.
- T. Chen, M. Hague, A. W. Lin, P. Rümmer and Z. Wu, "Decision procedures for path feasibility of string-manipulating programs with complex operations", Proceedings of the ACM on Programming Languages 3 (POPL), Article 49, 2019, doi:[10.1145/3290362](https://doi.org/10.1145/3290362); full version arXiv:1811.03167v1, <https://arxiv.org/abs/1811.03167v1>: Proposition 5.5 and Appendix C (hardness with automata-given regular constraints), cited only for the contrast in the statement.
