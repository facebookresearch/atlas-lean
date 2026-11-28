# Verifying a recursive upper bound of a partial recursive function is Π⁰₁-complete

For a fixed total recursive function $F$, the set of indices of partial recursive functions bounded by $F$ wherever they
are defined is $\Pi^0_1$-complete; in particular it is undecidable whether $F$ is an upper bound of a given program.

Fix a Gödel numbering $x \mapsto \varphi_x$, given by an effective listing of programs, of the partial recursive functions $\mathbb{N} \to \mathbb{N}$. A
*sup-interpretation* of a partial recursive function $f$ is a total recursive function $F$ with $F(z) \ge f(z)$ for every
$z$ at which $f(z)$ is defined. For a total recursive $F$ let

$$
SI(F) = \{\, x \in \mathbb{N} \mid \forall z\ \bigl(\varphi_x(z)\downarrow \implies \varphi_x(z) \le F(z)\bigr) \,\}.
$$

**Theorem.** For every total recursive function $F$, the set $SI(F)$ is $\Pi^0_1$-complete: it lies in the class
[$\Pi_1$ of the arithmetical hierarchy](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md), and the
$\Pi^0_1$-complete set $\{x \mid \varphi_x(0)\uparrow\}$ many-one reduces to it by a total computable function.

The source also shows that no total recursive function decides, for indices $x$ and $y$, whether
$\varphi_x(z) \le \varphi_y(z)$ wherever $\varphi_x(z)$ is defined; that the least index of a total bound cannot be computed;
that some partial recursive functions have no recursive sup-interpretation at all; and that the set of indices of partial
recursive functions that have a recursive sup-interpretation is in $\Sigma^0_3$ (without a matching lower bound).

## Depends on

- [The arithmetical class Πₙ](../../degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../decidable-and-recognizable-predicates/tm2-decidable.md)
- [Co-recognizability by multi-stack machines](../decidable-and-recognizable-predicates/tm2-co-recognizable.md)
- [Halting of a code on an input](../halting-problem-and-rice-s-theorem/halts.md)

## Proof depends on

- [The halting problem is not co-recognizable by multi-stack machines](../halting-problem-and-rice-s-theorem/not-tm2-co-recognizable-halting.md)

## Expansion

*Membership.* $x \in SI(F)$ iff for all $z$ and all $t$, either $\varphi_x(z)$ has not converged within $t$ steps, or it has
and its value is at most $F(z)$; the matrix is decidable because $F$ is total recursive.

*Hardness.* By the s-m-n theorem there is a total computable $f$ such that $\varphi_{f(x)}(z) = F(z) + 1$ if $\varphi_x(0)$
converges and $\varphi_{f(x)}(z)$ is undefined otherwise. Then $\varphi_x(0)\uparrow$ iff $\varphi_{f(x)}$ is nowhere
defined iff $f(x) \in SI(F)$.

## Sources

- R. Péchoux, "Synthesis of sup-interpretations: a survey", *Theoretical Computer Science* 467:30–52, 2013, doi:[10.1016/j.tcs.2012.11.003](https://doi.org/10.1016/j.tcs.2012.11.003). Numbering of the version read, arXiv:1210.7136v1: Definition 2 (sup-interpretation), Theorem 4 ($\Pi^0_1$-completeness of $SI(F)$), Theorem 1 (the s-m-n theorem), Theorems 2 and 3, Corollary 1 and Theorem 5 (the $\Sigma^0_3$ upper bound).
