# The two-tier value-1 problem for probabilistic automata is undecidable

No algorithm decides whether, for some finite words $u$ and $v$, a given probabilistic automaton accepts the words
$(u v^n)^{2^n}$ with probability tending to $1$.

Let $\mathcal{A}$ range over [probabilistic automata](../probabilistic-automata-and-cut-point-languages.md)
with acceptance probabilities $P_{\mathcal{A}}(w)$.

**Theorem.** The following problem is undecidable: given a probabilistic automaton $\mathcal{A}$ whose transition probabilities are rational numbers, given as fractions of integers, are there finite words $u, v$ (the empty word allowed)
such that

$$
\lim_{n \to \infty} P_{\mathcal{A}}\bigl((u v^n)^{2^n}\bigr) = 1 ?
$$

These *two-tier* sequences repeat $v$ a linear number of times and $u v^n$ an exponential number of times. A positive answer implies
that $\mathcal{A}$ has [value 1](../value-1-problem-for-probabilistic-automata.md), so the
problem asks for a very restricted kind of witness of value $1$; the source reads this as showing that undecidability of the value-1
problem arises when polynomial and exponential behaviors are combined, in contrast with the decidable case of the Markov Monoid
algorithm.

## Depends on

- [Probabilistic automata and cut-point languages](../probabilistic-automata-and-cut-point-languages.md)
- [Decidability by multi-stack machines](../../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The emptiness problem for probabilistic automata is undecidable](../emptiness-problem-for-probabilistic-automata.md)

## Expansion

The proof reuses the reduction of Gimbert and Oualhadj from emptiness to the value-1 problem with a refined analysis. From an
automaton $\mathcal{A}$ with transition probabilities $0$, $\frac{1}{2}$ or $1$, it builds an automaton $\mathcal{B}$ over the
alphabet of $\mathcal{A}$ extended with two letters, with two copies of the states of $\mathcal{A}$ and three further states, such
that some word $w$ has $P_{\mathcal{A}}(w) > \frac{1}{2}$ if and only if some two-tier sequence $(u v^n)^{2^n}$ has acceptance
probability in $\mathcal{B}$ tending to $1$. Emptiness, whether some word is accepted with probability above $\frac{1}{2}$, is
undecidable (Paz), and the reduction needs it for automata with transition probabilities $0$, $\frac12$ and $1$, which the proof
of Gimbert and Oualhadj gives (as the source notes before the construction). A good expansion adds and links a page for that
restricted emptiness result.

## Sources

- N. Fijalkow, "Profinite techniques for probabilistic automata and the Markov Monoid algorithm", *Theoretical Computer Science* 680:1–14, 2017, doi:10.1016/j.tcs.2017.04.006; Section 5 of the version arXiv:1501.02997v4: Theorem 7, "Undecidability of the two-tier value 1 problem", with its proof, in Section 5.1, and the discussion of its significance in Section 5.2 ("Combining the Two Results").
