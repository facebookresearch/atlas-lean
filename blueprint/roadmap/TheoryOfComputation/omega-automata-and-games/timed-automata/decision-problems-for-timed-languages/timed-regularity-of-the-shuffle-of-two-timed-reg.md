# Timed regularity of the shuffle of two timed regular languages is undecidable

No algorithm decides whether the shuffle of the timed languages of two given timed automata is again timed regular.

The *shuffle* of two elements $x, y$ of a monoid $M$ is the set $x \bowtie y$ of all products
$x_1 y_1 x_2 y_2 \cdots x_n y_n$ with $x = x_1 \cdots x_n$ and $y = y_1 \cdots y_n$ in $M$; for subsets,
$R_1 \bowtie R_2 = \bigcup \{x \bowtie y : x \in R_1,\ y \in R_2\}$. Take for $M$ the monoid $(\mathcal{R} \times \Sigma)^\star$
of [finite timed words](timed-automata-over-finite-timed-words.md), so that each letter keeps the delay attached to it.

**Theorem.** It is undecidable, given two timed automata $\mathcal{A}$ and $\mathcal{B}$ over finite timed words, whether
$L(\mathcal{A}) \bowtie L(\mathcal{B})$ is timed regular.

The class of timed regular languages is not closed under shuffle. Given $\mathcal{A}$ and $\mathcal{B}$, it is likewise
undecidable whether the shuffle is accepted by some timed automaton in $TA(n, K)$ for given $n, K$, by some timed automaton
with fewer than $n$ clocks for a given $n \ge 1$, or by some deterministic timed automaton.

## Depends on

- [Timed automata over finite timed words](timed-automata-over-finite-timed-words.md)

## Proof depends on

None.

## Expansion

Let $\Sigma = \{a, b\}$, let $R_1$ be the timed words $t_1 . a . 1 . a . t_2 . a$ with $t_1 + t_2 = 1$, and $R_2$ the timed words
$1 . b . s . b$ with $s > 0$; both are timed regular. Intersecting $R_1 \bowtie R_2$ with the timed regular language of the
words $t_1 . a . 1 . b . s . b . 1 . a . t_2 . a$ leaves those with $t_1 + t_2 = 1$, which no timed automaton accepts: after
reading $t_1 . a . 1 . b . s . b . 1 . a$ every clock holds $t_1 + s + 2$, $2 + s$, $1 + s$ or $1$, so none of them remembers
$t_1$. For undecidability, given $L = L(\mathcal{A})$ over $\Sigma$ and a new letter $c$, let $\mathcal{L}$ be the union of
$L . (\mathcal{R} \times \{c\}) . (\mathcal{R} \times \Sigma)^\star$, the timed words with no $c$ or at least two $c$'s, and
$(\mathcal{R} \times \Sigma)^\star . 1 . c . R_1$. If $L$ is universal, $\mathcal{L} \bowtie R_2$ is the set of all timed words
over $\Sigma \cup \{c\}$; otherwise a word $u \notin L$ forces $\mathcal{L} \bowtie R_2$ to contain, after $u . 1 . c$, the
non-regular language above, so it is not timed regular. This reduces the universality problem for timed automata over finite
timed words, which is undecidable (Alur and Dill).

## Sources

- O. Finkel, "Undecidable problems about timed automata", in *Formal Modeling and Analysis of Timed Systems (FORMATS 2006)*, Lecture Notes in Computer Science 4202, pp. 187–199, Springer, 2006, doi:10.1007/11867340_14; Section 5 of the version arXiv:0712.1363v1: the definition of the shuffle, Theorem 4 (non-closure), Theorem 5 with its proof, and the paragraph on Problems 1 to 3 that follows it.
