# Solomonoff's prior and the measure mixture

Solomonoff's prior $M(x)$ is the probability that a universal monotone Turing machine fed with uniformly random bits outputs a
string beginning with $x$; the measure mixture $\overline{M}$ keeps only the contribution of programs that output infinite strings.

Let $\mathcal{X}$ be a finite alphabet, $\mathcal{X}^*$ the finite and $\mathcal{X}^\infty$ the infinite strings over it, $\epsilon$ the
empty string, and $x \sqsubseteq y$ the prefix relation. A *semimeasure* is a function $\nu : \mathcal{X}^* \to [0, 1]$ with
$\nu(\epsilon) \le 1$ and $\nu(x) \ge \sum_{a \in \mathcal{X}} \nu(xa)$ for all $x$; it is a *measure* if both are equalities.

Fix a universal monotone Turing machine $U$, the reference machine. *Solomonoff's prior* is

$$
M(x) = \sum_{p \,:\, x \sqsubseteq U(p)} 2^{-|p|} ,
$$

the sum over the binary programs $p$ whose output starts with $x$. $M$ is a semimeasure but not a measure. The *measure mixture*
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

- J. Leike and M. Hutter, "On the computability of Solomonoff induction and knowledge-seeking", in *Algorithmic Learning Theory (ALT 2015)*, Lecture Notes in Computer Science 9355, pp. 364–378, Springer, 2015, doi:10.1007/978-3-319-24486-0_24; numbering of the version arXiv:1507.04124v1: Section 2.2 (strings), Definition 1 ($\Sigma^0_n$-, $\Pi^0_n$-, $\Delta^0_n$-computable functions) and the beginning of Section 3 (semimeasures, Solomonoff's prior, the measure mixture, conditional probabilities).
- M. Li and P. Vitányi, *An Introduction to Kolmogorov Complexity and Its Applications*, 3rd ed., Springer, 2008: the section on continuous sample spaces (universal monotone machines and Solomonoff's prior); this book was not read here, so it is cited by topic.
