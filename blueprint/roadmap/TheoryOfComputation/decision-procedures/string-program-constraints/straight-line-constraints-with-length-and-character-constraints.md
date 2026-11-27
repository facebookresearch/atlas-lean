# Straight-line constraints with length and character constraints

Satisfiability of straight-line string constraints with concatenation and transducers stays in EXPSPACE when Boolean combinations of linear constraints over lengths, letter counts and integer variables, and Boolean combinations of letter comparisons at positions, are added.

Let $\Sigma$ be a finite alphabet. Besides string variables, use integer variables ranging over $\mathbb{N}$.

- An *atomic integer constraint* is $a_1 t_1 + \dots + a_n t_n \le d$ with integer constants $a_1, \dots, a_n, d$ written in binary, where each term $t_i$ is an integer variable $u$, the length $|x|$ of a string variable $x$, or the number $|x|_a$ of occurrences of a letter $a \in \Sigma$ in $x$. An *integer constraint* is a Boolean combination of atomic ones.
- An *atomic character constraint* is $x[u] = y[v]$, where each of $x, y$ is a string variable or a constant word and each of $u, v$ is an integer variable or a positive integer constant; $x[u]$ denotes the $u$-th letter of $x$, positions counted from $1$. A *character constraint* is a Boolean combination of atomic ones.
- The class $\mathrm{SL}_e$ consists of the formulas $\psi = \varphi \wedge \theta_{\mathrm{int}} \wedge \theta_{\mathrm{char}}$ with $\varphi$ a [straight-line string constraint](straight-line-string-constraints.md), $\theta_{\mathrm{int}}$ an integer constraint and $\theta_{\mathrm{char}}$ a character constraint.

An assignment $\iota$ maps string variables to words and integer variables to natural numbers. It satisfies $\psi$ only if, for **every** term $x[u]$ occurring anywhere in $\psi$ (also under a negation, or in a disjunct that is not needed), the position is valid, $1 \le \iota(u) \le |\iota(x)|$; an assignment violating this guard satisfies no formula containing that term. When all positions are valid, $\psi$ is evaluated as usual, with $x[u]$ read as the letter of $\iota(x)$ at position $\iota(u)$. The size of an assignment is the total length of its words plus the total bit-length of its integers. Then:

1. Satisfiability of $\mathrm{SL}_e$ is in [EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md).
2. There is a polynomial $p$ such that every satisfiable formula $\psi$ of $\mathrm{SL}_e$ has a solution of size at most $2^{2^{p(|\psi|)}}$.

This decidability concerns straight-line constraints only: for unrestricted word equations with linear length constraints, decidability is a long-standing open problem that neither source settles, and adding letter counting to word equations is undecidable (Büchi and Senger, as cited by Chen et al.). The guard is formula-wide; the replaceAll setting of Chen et al. instead makes an atom with an invalid position false, which behaves differently under negation.

## Depends on

- [Straight-line string constraints](straight-line-string-constraints.md)
- [The class EXPSPACE](../../complexity-classes/time-and-space-complexity-classes/expspace.md)

## Proof depends on

- [Straight-line transducer constraints are EXPSPACE-complete](straight-line-transducer-constraints-are-expspace-complete.md)
- [Acyclic transducer constraints are PSPACE-complete](acyclic-transducer-constraints-are-pspace-complete.md)
- [Savitch's theorem](../../complexity-classes/savitch.md)

## Expansion

This node still needs its proof broken down; the source proof (Section 5.1) has these parts.

Transformation (Section 5.1.1). Apply Steps 1–2 of the EXPSPACE procedure for straight-line constraints, so that each string variable $y$ is spelled by copies $y(1), \dots, y(\max_y)$, and replace $|y|$ by $\sum_i |y(i)|$ and $|y|_a$ by $\sum_i |y(i)|_a$. In a character term, a constant word is first replaced by a fresh string variable constrained by the singleton membership $\in \{w\}$ (integer constraints alone cannot fix a word, since $ab$ and $ba$ have the same length and letter counts), and a constant position $c$ by a fresh integer variable $u$ with the integer equality $u = c$. A term $x[u]$ then falls into exactly one copy: guess $i$, replace $x[u]$ by $x(i)[u']$ for a fresh integer variable $u'$, and add $u = u' + \sum_{j < i} |x(j)|$ together with the in-copy guard $1 \le u' \le |x(i)|$. Guessing the disjuncts of the splits yields, in nondeterministic exponential time, a concatenation-free formula $\varphi'$ of the class $\mathrm{SL}^e_r$ (transducer and regular atoms forming a forest, with integer and character constraints), satisfiable iff $\psi$ is, with solutions translated by reassembling copies.

Bounded models for the concatenation-free core (Lemma 13, stated in Section 5.1.2 and proved in Section 5.1.4). If $\varphi'$ is satisfiable it has a solution with words of length exponential in $|\varphi'|$ and integers of bit-length polynomial in $|\varphi'|$. Route: the synchronized multi-track transducer recognizing the string part (Proposition 14, the construction of the acyclic page) is turned into a monotonic counter machine whose counters record letter counts per track, guessed integer values and guessed positions of the character terms, with flags freezing a position once its letter is fixed (Lemma 15); the reachable configurations of such a machine are a disjunction of existential Presburger formulas of size polynomial in the number of counters and the logarithm of the number of states (Proposition 16, after Kopczyński and To), and small solutions of existential Presburger formulas (Scarpellini) bound the integers and hence the word lengths.

Decision (Section 5.1.3). For $\varphi'$, guess the characters and the integer values (polynomially many bits), check the integer and character constraints, and then guess the solution tuple letter by letter on the fly through the multi-track transducer, keeping a binary counter for each length and letter count and checking, when the track of $x$ reaches each guessed position, that the letter read there is the guessed character, until a final state is reached with the guessed counts. This is nondeterministic polynomial space in $|\varphi'|$, hence deterministic by Savitch's theorem; since $|\varphi'|$ is exponential in $|\psi|$, the whole procedure runs in exponential space. Part 2 follows from Lemma 13 as Theorem 6 follows from the acyclic bound.

The source states only the upper bound for $\mathrm{SL}_e$. Since $\mathrm{SL}_e$ contains the straight-line string constraints, which are [EXPSPACE-complete](straight-line-transducer-constraints-are-expspace-complete.md), satisfiability of $\mathrm{SL}_e$ is also EXPSPACE-hard; this is a direct consequence, not a separately cited result.

## Sources

- A. W. Lin and P. Barceló, "String solving with word equations and transducers: towards a logic for analysing mutation XSS", POPL 2016, pp. 123–136, doi:[10.1145/2837614.2837641](https://doi.org/10.1145/2837614.2837641); full version arXiv:1511.01633v1, <https://arxiv.org/abs/1511.01633v1>: Section 5, Definitions 5–7 and the paragraph after Definition 7 (validity of positions), Theorem 12, Section 5.1.1, Section 5.1.2 (Lemma 13), Section 5.1.3 (Proposition 14 and the on-the-fly algorithm), Section 5.1.4 (proof of Lemma 13: the monotonic counter machine, Lemma 15, Proposition 16 after Kopczyński and To, and Scarpellini's bound, references [41], [63] and [59] there).
- T. Chen, Y. Chen, M. Hague, A. W. Lin and Z. Wu, "What is decidable about string constraints with the ReplaceAll function", Proceedings of the ACM on Programming Languages 2 (POPL), Article 3, 2018, doi:[10.1145/3158091](https://doi.org/10.1145/3158091); full version arXiv:1711.03363v1, <https://arxiv.org/abs/1711.03363v1>: Definition 9.2 (atom-level falsity for invalid positions) and Section 10 (the open problem of word equations with length constraints; letter counting undecidable, citing Büchi and Senger).
