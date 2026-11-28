# Solomonoff's prior and the measure mixture

Solomonoff's prior $M(x)$ is the probability that a universal monotone Turing machine fed with uniformly random bits outputs a
string beginning with $x$; the measure mixture $\overline{M}$ keeps only the contribution of programs that output infinite strings.

Let $\mathcal{X}$ be a finite alphabet with at least two symbols (the source fixes only a finite alphabet, but its constructions output two distinct symbols $0$ and $1$; over a one-letter alphabet the measure mixture is constant and the source's proofs do not apply), $\mathcal{X}^*$ the finite and $\mathcal{X}^\infty$ the infinite strings over it, $\epsilon$ the
empty string, and $x \sqsubseteq y$ the prefix relation. A *semimeasure* is a function $\nu : \mathcal{X}^* \to [0, 1]$ with
$\nu(\epsilon) \le 1$ and $\nu(x) \ge \sum_{a \in \mathcal{X}} \nu(xa)$ for all $x$; it is a *measure* if both are equalities.

A *monotone machine* $T$ is a Turing machine with a one-way read-only binary input tape and a one-way write-only output tape over $\mathcal{X}$; on a finite or infinite binary input $p$ it outputs the string $T(p) \in \mathcal{X}^* \cup \mathcal{X}^\infty$ written while it reads $p$, so output already written is never taken back: $T(p) \sqsubseteq T(pq)$. A monotone machine $U$ is *universal* if for every monotone machine $T$ there is a binary string $q_T$ with $U(q_T p) = T(p)$ for all $p$; this is the sense in which the source's proof of Theorem 4 calls a machine running $U(p)$ on input $00p$ universal.

Fix a universal monotone machine $U$, the reference machine. *Solomonoff's prior* $M(x)$ is the probability that $U$ outputs a string beginning with $x$ when its input is an infinite sequence $\omega \in \{0, 1\}^{\mathbb{N}}$ of independent uniformly random bits:

$$
M(x) = \lambda\{ \omega \in \{0, 1\}^{\mathbb{N}} : x \sqsubseteq U(\omega) \} = \sum_{p \in P_x} 2^{-|p|} ,
$$

where $\lambda$ is the uniform measure and $P_x$ is the set of *minimal* programs for $x$, the finite binary strings $p$ with $x \sqsubseteq U(p)$ such that no proper prefix $q$ of $p$ has $x \sqsubseteq U(q)$. The source writes the sum over all $p$ with $x \sqsubseteq U(p)$ as shorthand; since every extension of such a $p$ also qualifies, only the minimal ones are counted, and $P_x$ is prefix-free, so $M(x) \le 1$. $M$ is a semimeasure, a function $\nu : \mathcal X^* \to [0, 1]$ with $\nu(\epsilon) \le 1$ and $\nu(x) \ge \sum_{a \in \mathcal X} \nu(xa)$ for every $x$, but not a measure, for which these inequalities are equalities. The *measure mixture*
is

$$
\overline{M}(x) = \lim_{n \to \infty} \sum_{y \in \mathcal{X}^n} M(xy) ,
$$

which drops the contribution of programs that output only a finite string. The conditional versions are
$M(xy \mid x) = M(xy) / M(x)$ and similarly for $\overline{M}$; they are well defined since $M(x) > 0$ for all $x$. All these
quantities depend on the reference machine $U$; when it matters it is written as a subscript, $M_U$ and $\overline{M}_U$.

A function $f : \mathcal{X}^* \to \mathbb{R}$ is *$\Sigma^0_n$-computable* ($\Pi^0_n$-, $\Delta^0_n$-computable) if the set
$\{(x, q) : f(x) > q\}$, with $q$ ranging over the rationals, is in the class $\Sigma^0_n$ ($\Pi^0_n$, $\Delta^0_n$) of the
[arithmetical hierarchy](../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md). *Lower semicomputable* means
$\Sigma^0_1$-computable, and *limit computable* means $\Delta^0_2$-computable. $M$ is lower semicomputable and not computable.

## Depends on

- [The arithmetical class Σₙ](../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The class Δₙ of the arithmetical hierarchy](../../degrees-and-hierarchies/arithmetical-hierarchy/is-delta.md)
- [Recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Sources

- J. Leike and M. Hutter, "On the computability of Solomonoff induction and knowledge-seeking", in *Algorithmic Learning Theory (ALT 2015)*, Lecture Notes in Computer Science 9355, pp. 364–378, Springer, 2015, doi:10.1007/978-3-319-24486-0_24; numbering of the version arXiv:1507.04124v1: Section 2.2 (strings), Definition 1 ($\Sigma^0_n$-, $\Pi^0_n$-, $\Delta^0_n$-computable functions), the beginning of Section 3 (semimeasures, Solomonoff's prior as the probability of output starting with $x$ on uniformly random input bits, Eq. (2), the measure mixture, conditional probabilities) and the proof of Theorem 4 (the universal machine $U'$ built from $U$).
