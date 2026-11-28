# Solvability of subword history equations is undecidable

No algorithm decides, given two subword histories, whether some word gives them equal values. This holds already for
letter-restricted subword histories over a fixed alphabet of nine letters.

Let `SubwordEqSolvability` be the problem: given a finite alphabet $\Sigma$ and two
[subword histories](subword-histories.md) $SH_1$ and $SH_2$ in $\Sigma$, decide whether there is a word $w \in \Sigma^*$
(the empty word allowed) with

$$
|w|_{SH_1} = |w|_{SH_2}.
$$

**Theorem.** `SubwordEqSolvability` is undecidable. It remains undecidable when the alphabet is fixed to have nine letters
and both subword histories are restricted to be letter-restricted.

In the first statement the alphabet is part of the input (the proof uses one letter per variable of a Diophantine
equation). The source also states the conditional form: if solvability of Diophantine equations is undecidable for $n$
variables, then the problem is undecidable for letter-restricted subword histories over an $n$-letter alphabet; the nine
comes from Matiyasevich's nine-variable bound. The source does not settle alphabets of at most eight letters, and it
states that equivalence of two subword histories is decidable (Mateescu, Salomaa and Yu).

## Depends on

- [Subword histories](subword-histories.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Reduce Hilbert's tenth problem. Given a Diophantine equation $\sum_{i=1}^{\ell} c_i x_1^{e_{i,1}} \cdots x_m^{e_{i,m}} = 0$, take
$\Sigma = \{a_1, \dots, a_m\}$ and the letter-restricted subword history

$$
SH = \sum_{i=1}^{\ell} c_i \Bigl(\prod^{e_{i,1}} a_1 \times \cdots \times \prod^{e_{i,m}} a_m\Bigr).
$$

Since $|w|_{a_j}$ is the number of occurrences of $a_j$ in $w$, the value $|w|_{SH}$ is the polynomial evaluated at the
Parikh vector of $w$, and every vector of natural numbers is the Parikh vector of some word. So the instance $(SH, 0 \cdot \lambda)$
has a solution exactly when the equation has a solution in natural numbers (the letter counts may be zero, so the reduction
is from solvability in natural numbers, which is undecidable as well). The construction keeps the number of variables, which
gives the nine-letter bound from a nine-variable undecidable family of Diophantine equations. A good expansion links a page for the undecidability of solvability in natural numbers of Diophantine equations in nine variables.

## Sources

- S. Seki, "Absoluteness of subword inequality is undecidable", *Theoretical Computer Science* 418:116–120, 2012, doi:[10.1016/j.tcs.2011.10.017](https://doi.org/10.1016/j.tcs.2011.10.017). Numbering of the version read, arXiv:1108.2758v1: Theorem 1 (undecidability), Theorem 2 (the conditional form for n letters) and Corollary 2 (nine letters, letter-restricted), with the nine-variable bound for Diophantine equations recalled from Matiyasevich in the paragraph before Theorem 2.
