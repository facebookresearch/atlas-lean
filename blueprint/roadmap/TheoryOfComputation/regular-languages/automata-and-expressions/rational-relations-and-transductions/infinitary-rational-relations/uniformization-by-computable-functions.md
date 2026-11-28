# Uniformizing infinitary rational relations by computable functions is undecidable

No algorithm decides whether a relation between infinite words accepted by a Büchi transducer has a computable uniformizer, a function picking for every input in its domain an output related to it; the same holds for continuous, sequential and letter-to-letter sequential uniformizers.

Let $R\subseteq\Sigma^\omega\times\Gamma^\omega$ be an [infinitary rational relation](infinitary-rational-relations-and-omega-rational.md). A partial function $f:\Sigma^\omega\to\Gamma^\omega$ *uniformizes* $R$ if $\mathrm{dom}(f)=\mathrm{dom}(R)$ and $(\alpha,f(\alpha))\in R$ for every $\alpha\in\mathrm{dom}(R)$. A function $f$ is *computable* if a deterministic machine with a one-way read-only input tape, a two-way work tape and a one-way write-only output tape, visiting every input cell, produces for every $\alpha\in\mathrm{dom}(f)$ and every $i$, after reading some finite prefix of $\alpha$, an output extending the first $i$ letters of $f(\alpha)$ (Weihrauch). A function is *sequential* if a deterministic finite-state transducer computes it, and *letter-to-letter sequential* if that transducer outputs exactly one letter per input letter.

**Theorem.**
1. It is undecidable, given a Büchi transducer, whether its infinitary rational relation is uniformized by some computable function, even for relations with total domain $\Sigma^\omega$.
2. It is undecidable whether it is uniformized by some sequential function, respectively by some letter-to-letter sequential function, even for relations with total domain; the reduction also covers continuous uniformizers.

The source shows that synthesis of a computable uniformizer becomes decidable for deterministic rational relations, recognized by deterministic two-tape parity automata.

## Depends on

- [Infinitary rational relations and ω-rational functions](infinitary-rational-relations-and-omega-rational.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)
- [Halting is undecidable](../../../../computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Item 1 is proved by a reduction from Post's correspondence problem. Item 2, and item 1 again, follow from a reduction from the halting problem on the empty tape: for a deterministic Turing machine $M$, the relation $R_M$ relates inputs $c_0\#c_1\#\cdots c_n\#\alpha'$, with $c_0$ initial and $c_n$ halting, to outputs with the same configuration sequence when $\alpha'$ has infinitely many $a$'s, and to outputs whose configuration sequence contains a successor error when it has finitely many; it is total and $\omega$-rational. If $M$ does not halt, every encoded sequence has an error, so the identity, which is letter-to-letter sequential, uniformizes $R_M$. If $M$ halts with an error-free run $u$, any continuous uniformizer must output $u$ on $ua^\omega$ but an erroneous sequence on $ua^jb^\omega$ for every $j$, contradicting continuity at $ua^\omega$. Since letter-to-letter sequential, sequential and computable functions are continuous, all four questions are undecidable.

## Sources

- Emmanuel Filiot and Sarah Winter, "Synthesizing Computable Functions from Rational Specifications Over Infinite Words", *International Journal of Foundations of Computer Science* 35(01n02), 2024, pp. 179–214, doi:[10.1142/S012905412348009X](https://doi.org/10.1142/S012905412348009X), and in *FSTTCS 2021*, LIPIcs 213, 2021, pp. 43:1–43:16, doi:[10.4230/LIPIcs.FSTTCS.2021.43](https://doi.org/10.4230/LIPIcs.FSTTCS.2021.43); read in arXiv:2103.05674v4 ([arXiv](https://arxiv.org/abs/2103.05674v4)), whose numbering is used: the problem statement and Proposition 5 with its proof sketch in Section 2 (Preliminaries), and Proposition 31 with its proof in Section 6 (Discussion).
