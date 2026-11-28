# Whether a k-automatic set of rationals contains a power of k is undecidable

For every base $k \ge 2$, no algorithm decides whether the set of rational numbers represented by the pairs of base-$k$ numerals accepted by a given
finite automaton contains a power of $k$.

For $k \ge 2$ let $\Sigma_k = \{0, 1, \dots, k-1\}$ and, for $w \in \Sigma_k^*$, let $[w]_k$ be the integer that $w$ represents in base $k$, most significant digit first. A finite automaton $M$ over the alphabet $\Sigma_k \times \Sigma_k$ reads pairs
of numerals of equal length; for an accepted word $x$ let $\pi_1(x)$ and $\pi_2(x)$ be its two components. The set of rationals represented by $M$ is

$$
\mathrm{quo}_k(M) = \left\{ \frac{[\pi_1(x)]_k}{[\pi_2(x)]_k} : x \in L(M) \right\},
$$

where words whose second component represents $0$ (including the empty word) contribute nothing, since the quotient is undefined for them (the source leaves this convention implicit); a set of nonnegative rationals is *$k$-automatic* if it is $\mathrm{quo}_k(M)$ for some such automaton $M$.

**Theorem.**

1. It is undecidable, given $k \ge 2$ and a finite automaton $M$ over $\Sigma_k \times \Sigma_k$, whether $\mathrm{quo}_k(M)$ contains a power $k^i$ with $i \ge 0$ (Theorem 5).
2. For every fixed $k \ge 2$, the same problem with only $M$ as input is undecidable (Theorem 6).

## Depends on

- [Encoded NFA](../../../decision-procedures/encoded-finite-automata/encoded-nfa.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Whether a two-tape automaton accepts a word paired with a cyclic shift is undecidable](shifted-words-accepted-by-automata.md)

## Expansion

Item 1 reuses the construction for the problem whether an automaton over pairs accepts a word $x c^n \times c^n x$: after renaming the letters of $\Gamma$ as the digits $1, \dots, \ell$ and $c$ as $0$, and taking $k = \ell + 1$, an accepted word
represents a power of $k$ exactly when it has the form $x 0^n \times 0^n x$. Both rest on the undecidability of the problem whether a length-preserving string rewriting system rewrites $a^n$ into $b^n$ for some $n \ge 1$ (Lemma 1 of the source).
Item 2 recodes all words over $\{0, 1\}$ by the morphism $c \mapsto 0^{m+1}$, $a_i \mapsto 1^i 0^{m-i} 1$, which removes the dependence of the base on the alphabet.

## Sources

- J. Endrullis, J. Shallit and T. Smith, "Undecidability and finite automata", in *Developments in Language Theory (DLT 2017)*, Lecture Notes in Computer Science 10396, pp. 160–172, Springer, 2017, doi:10.1007/978-3-319-62809-7_11; read in arXiv:1702.01394v2, whose numbering is used here: Theorems 5 and 6 in Section 4 with their proofs, Lemma 1 in Section 2 and Theorem 2 in Section 3.
