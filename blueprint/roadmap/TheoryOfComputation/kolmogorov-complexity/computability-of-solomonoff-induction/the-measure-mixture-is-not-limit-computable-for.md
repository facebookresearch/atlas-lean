# The measure mixture is not limit computable for some universal machine

For some universal monotone machine, the measure mixture $\overline{M}$, the part of Solomonoff's prior coming from programs that
output infinite strings, is not limit computable: the set of pairs $(x, q)$ with $\overline{M}(x) > q$ is not in $\Delta^0_2$.

**Theorem.** There is a [universal monotone machine](solomonoff-s-prior-and-the-measure-mixture.md) $U'$ such that the set

$$
\{ (x, q) : \overline{M}_{U'}(x) > q \} ,
$$

with $x$ a finite string and $q$ a rational number, is not in $\Delta^0_2$, where $\overline{M}_{U'}$ is the
[measure mixture](solomonoff-s-prior-and-the-measure-mixture.md) for the reference machine $U'$.

The statement is existential in the reference machine. For every universal machine the source shows that $\overline{M}$ is
$\Pi^0_2$-computable, so for $U'$ it is $\Pi^0_2$-computable but not $\Delta^0_2$-computable. For the normalized measure mixture
$\overline{M}_{\mathrm{norm}} = \overline{M} / \overline{M}(\epsilon)$ there is likewise a universal machine for which the set
$\{(x, q) : \overline{M}_{\mathrm{norm}}(x) > q\}$ is in neither $\Sigma^0_2$ nor $\Pi^0_2$.

## Depends on

- [Solomonoff's prior and the measure mixture](solomonoff-s-prior-and-the-measure-mixture.md)
- [The class Δₙ of the arithmetical hierarchy](../../degrees-and-hierarchies/arithmetical-hierarchy/is-delta.md)
- [The arithmetical class $\Pi_n$](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

None.

## Expansion

Take a set $A$ in $\Pi^0_2$ but not in $\Delta^0_2$, with $n \in A$ iff $\forall k\, \exists i\, S(n, k, i)$ for a computable relation
$S$. The program $p_n$ outputs $1^{n+1}0$ and then, for $k = 0, 1, 2, \dots$, searches for an $i$ with $S(n, k, i)$ and outputs one
more $0$ each time a search succeeds; so $p_n$ outputs the infinite string $1^{n+1}0^\infty$ exactly when $n \in A$. Define $U'$ by
letting the input $1^{n+1}0$ run $p_n$, the input $00p$ run $U(p)$, and the input $01p$ run $U(p)$ with its output bitwise inverted;
$U'$ is universal. Then $\overline{M}_{U'}(1^{n+1}0) - \overline{M}_{U'}(0^{n+1}1)$ equals $2^{-n-2}$ if $n \in A$ and $0$ otherwise,
so a limit computation of $\overline{M}_{U'}$ would make $A$ limit computable.

## Sources

- J. Leike and M. Hutter, "On the computability of Solomonoff induction and knowledge-seeking", in *Algorithmic Learning Theory (ALT 2015)*, Lecture Notes in Computer Science 9355, pp. 364–378, Springer, 2015, doi:10.1007/978-3-319-24486-0_24; numbering of the version arXiv:1507.04124v1: Theorem 4 with its proof, Theorem 3 (v) ($\overline{M}$ is $\Pi^0_2$-computable) and Corollary 5 (the normalized measure mixture).
