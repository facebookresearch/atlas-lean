# The reverse Post correspondence problem with a regular filter is undecidable

No algorithm decides whether a finite set of dominoes has a solution in a given regular language for the reverse Post correspondence problem, in which the upper word must be the
reversal of the lower word; for a unary alphabet the reverse problem without a filter is decidable.

Let $D = \{d_1, \dots, d_n\}$ be a finite set of dominoes $d_i = (\alpha_i, \beta_i) \in \Sigma^* \times \Sigma^*$. For a sequence $w = d_{i_1} \cdots d_{i_k} \in D^*$, its *upper word* is $u(w) = \alpha_{i_1} \cdots \alpha_{i_k}$ and its
*lower word* is $\ell(w) = \beta_{i_1} \cdots \beta_{i_k}$, as in the classical [Post correspondence problem](exists-not-tm2-decidable-pcp.md). A *solution of the reverse PCP* is a sequence $w \in D^+$ with
$u(w) = \ell(w)^R$, where $x^R$ is the reversal of $x$. In the *opposite direction PCP* the lower parts are placed from right to left, $\ell'(w) = \beta_{i_k} \cdots \beta_{i_1}$, and a solution is a $w \in D^+$ with
$u(w) = \ell'(w)$; replacing each $\beta_i$ by its reversal shows that the two problems are equivalent.

**Theorem.** It is undecidable, given a finite set $D$ of dominoes and a regular language $L$ (the *regular filter*), whether the opposite direction PCP for $D$ has a solution belonging to $L$;
equivalently, whether the reverse PCP for $D$ has a solution belonging to $L$. In the proof, the filter constrains the common word written by the solution.

For dominoes over a unary alphabet, the reverse PCP (without a filter) is decidable; whether the filter can be removed in general is left open. The source uses the construction to show that emptiness is undecidable for $5' \to 3'$ string assembly systems,
a model of DNA strand assembly in which the two strands grow in opposite directions, and that every recursively enumerable language is the image under an erasing morphism of the language of such a
system.

## Depends on

- [Domino (Post correspondence problem)](domino.md)
- [Decidability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof encodes the accepting computations of a Turing machine. Reading left to right, the upper strand writes the sequence of configurations $c_1, \dots, c_n$ of a computation, while the lower strand, built
from right to left, writes the same configurations so that the matching condition forces each configuration to be followed by its successor. The regular filter, built over marked copies of the tape symbols with separator symbols, restricts solutions to well-formed encodings, so a solution in the filter exists exactly when the machine has an accepting computation.

## Sources

- B. Nagy, "Reverse Post correspondence problem and undecidability of $5' \to 3'$ string assembly systems", *Electronic Proceedings in Theoretical Computer Science* 451, pp. 245–260, 2026, doi:10.4204/EPTCS.451.17; read in arXiv:2608.24257v1: Theorem 5 (opposite direction PCP with regular filter, Section 3.1) and Corollary 1 (reverse PCP), Theorem 4 (equivalence of the two problems, Section 3), Theorems 6 and 7 of Section 4 on $5' \to 3'$ string assembly systems, and Proposition 2 (the unary case) in Section 5, with the numbering of that version.
