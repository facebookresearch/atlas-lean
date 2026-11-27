# replaceAll with length constraints is undecidable

Adding one length equation $|x| = |y|$ to straight-line replaceAll constraints with single-letter patterns and variable replacements makes satisfiability undecidable, since replaceAll then multiplies numbers written in unary; character or indexOf constraints have the same effect.

Work in the single-letter case of [straight-line replaceAll constraints](straight-line-replaceall-constraints.md) (every pattern one letter; subjects and replacements variables or constants), and add constraints over integer variables ranging over $\mathbb{N}$:

- *integer constraints*: Boolean combinations of $a_1 t_1 + \dots + a_n t_n \le d$ with integer constants in binary, each $t_i$ an integer variable, a length $|x|$, or a letter count $|x|_a$;
- *character constraints*: Boolean combinations of atoms $x[t_1] = y[t_2]$, where $x, y$ are string variables or constant words, $t_1, t_2$ integer variables or positive constants, and $x[t]$ is the $t$-th letter of $x$ counting from $1$; an atom is false when one of its positions does not exist (the atom, not the whole formula);
- *indexOf constraints*: Boolean combinations of $t \ge \mathrm{IndexOf}(s_1, s_2)$ and $t \le \mathrm{IndexOf}(s_1, s_2)$, where $s_1, s_2$ are string variables or constant words, $t$ is an integer variable, a positive integer constant or $0$, and $\mathrm{IndexOf}(s_1, s_2)$ is the first position (from $1$) at which $s_1$ occurs in $s_2$, and $0$ if it does not occur.

Then satisfiability is undecidable for each of the following extensions:

1. with integer constraints, even if the only integer constraint is a single equation $|x| = |y|$, or a single equation $|x|_a = |y|_a$;
2. with character constraints only, or with indexOf constraints only.

The source also states undecidability with integer constraints when the straight-line part has a dependency graph of depth at most one (its Theorem 9.5); that claim is not included here, because its proof rests on a Diophantine normal form (its Theorem G.1) whose reference is unresolved in the source.

By contrast, length and letter-count constraints keep [straight-line transducer constraints](straight-line-constraints-with-length-and-character-constraints.md) decidable; there replaceAll can only have constant replacements and cannot multiply.

## Depends on

- [Straight-line replaceAll constraints](straight-line-replaceall-constraints.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

This node still needs its proof broken down; the source proofs (Appendix G) have these parts.

Part 1 reduces Hilbert's tenth problem in the form: do two polynomials $f, g$ with natural coefficients agree at some point of $\mathbb{N}^n$? (Undecidable by the DPRM theorem, moving negative coefficients to the other side.) Represent $k \in \mathbb{N}$ by the word $a^k$ over the one-letter alphabet $\{a\}$, with source variables $x_1, \dots, x_n \in a^*$. Addition is concatenation, multiplication of the numbers held by $x$ and $y$ is $\mathrm{replaceAll}(x, a, y)$, and constants are constant words, so straight-line formulas compute $y_f = a^{f(x)}$ and $y_g = a^{g(x)}$ sharing only source variables; concatenation is then expressed by replaceAll at the cost of two fresh letters, which do not survive in $y_f, y_g$. The equation $|y_f| = |y_g|$ (equivalently $|y_f|_a = |y_g|_a$) holds iff $f(x) = g(x)$.

Part 2 encodes $|y_f| = |y_g|$ from part 1: with a fresh letter $\sharp$, $z_f = y_f \sharp$ and $z_g = y_g \sharp$, the character constraint $z_f[n] = \sharp[1] \wedge z_g[n] = \sharp[1]$ forces equal lengths (using atom-level falsity at invalid positions); and over a one-letter alphabet $|x| = |y|$ iff $1 = \mathrm{IndexOf}(x, y) \wedge 1 = \mathrm{IndexOf}(y, x)$.

## Sources

- T. Chen, Y. Chen, M. Hague, A. W. Lin and Z. Wu, "What is decidable about string constraints with the ReplaceAll function", Proceedings of the ACM on Programming Languages 2 (POPL), Article 3, 2018, doi:[10.1145/3158091](https://doi.org/10.1145/3158091); full version arXiv:1711.03363v1, <https://arxiv.org/abs/1711.03363v1>: Section 1 (contributions), Section 9, Definitions 9.1–9.3, Theorem 9.4, Theorem 9.5, Proposition 9.6, and Appendix G (proof of Theorem 9.4, Propositions G.2 and G.3; Theorem 9.5 and Theorem G.1 noted only).
