# Conditional Solomonoff probability is not lower semicomputable

The conditional probability $M(xy \mid x) = M(xy) / M(x)$ of Solomonoff's prior is not lower semicomputable: the set of triples
$(x, xy, q)$ with $M(xy \mid x) > q$ is not recursively enumerable.

**Theorem.** Over an alphabet $\mathcal X$ with at least two symbols, for [Solomonoff's prior](solomonoff-s-prior-and-the-measure-mixture.md) $M$, the set

$$
\{ (x, xy, q) : M(xy \mid x) > q \} ,
$$

with $x, y$ finite strings and $q$ a rational number, is not recursively enumerable. Thus $M(xy \mid x)$ is not lower
semicomputable, although $M$ itself is lower semicomputable.

The source also shows that $M(xy \mid x)$ is limit computable, so it lies in $\Delta^0_2$ without being $\Sigma^0_1$-computable.

## Depends on

- [Solomonoff's prior and the measure mixture](solomonoff-s-prior-and-the-measure-mixture.md)
- [Recognizability by multi-stack machines](../../computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [The arithmetical class $\Sigma_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [The class Δₙ of the arithmetical hierarchy](../../degrees-and-hierarchies/arithmetical-hierarchy/is-delta.md)

## Proof depends on

None.

## Expansion

By a result of Lattimore, Hutter and Gavane, there is an infinite string $z$ with $z_{2t} = z_{2t-1}$ for all $t > 0$ such that
$\liminf_{t} M(z_{1:2t} \mid z_{<2t}) < 1$: $M$ does not learn that every even-numbered symbol repeats its predecessor. If
$M(xy \mid x)$ were lower semicomputable, the semimeasure $\nu$ that predicts the odd-numbered symbols according to $M$ and puts
probability $1$ on repeating them would be lower semicomputable, so $M \ge c\,\nu$ for some constant $c > 0$ by universal dominance.
The chain rule then gives $c \le \prod_{k \le t} M(z_{1:2k} \mid z_{<2k})$ for all $t$, while the right-hand side tends to $0$. A good expansion adds pages for the result of Lattimore, Hutter and Gavane on the string $z$ and for the universal dominance of $M$ over lower semicomputable semimeasures.

## Sources

- J. Leike and M. Hutter, "On the computability of Solomonoff induction and knowledge-seeking", in *Algorithmic Learning Theory (ALT 2015)*, Lecture Notes in Computer Science 9355, pp. 364–378, Springer, 2015, doi:10.1007/978-3-319-24486-0_24; numbering of the version arXiv:1507.04124v1: Theorem 6 with its proof and Theorem 3 (ii) (conditional $M$ is limit computable).
