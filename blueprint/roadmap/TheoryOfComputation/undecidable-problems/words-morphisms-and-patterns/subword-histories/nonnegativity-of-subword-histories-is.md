# Nonnegativity of subword histories is undecidable

No algorithm decides whether a given subword history takes only nonnegative values on all words. This answers a question of
Mateescu, Salomaa and Yu, and holds already for letter-restricted subword histories over nine letters.

Let `SubwordIneqAbsoluteness` be the problem: given a finite alphabet $\Sigma$ and a [subword history](subword-histories.md)
$SH$ in $\Sigma$, decide whether

$$
|w|_{SH} \ge 0 \quad \text{for every } w \in \Sigma^*.
$$

**Theorem.** `SubwordIneqAbsoluteness` is undecidable. It remains undecidable when the alphabet is fixed to have nine letters
and the subword history is restricted to be letter-restricted.

Replacing $\ge 0$ by $> 0$ does not change decidability, since $|w|_{SH} > 0$ for all $w$ exactly when
$|w|_{SH - \lambda} \ge 0$ for all $w$. By contrast, equivalence of subword histories is decidable (Mateescu, Salomaa and
Yu).

## Depends on

- [Subword histories](subword-histories.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Solvability of subword history equations is undecidable](solvability-of-subword-history-equations-is.md)

## Expansion

The complement of `SubwordEqSolvability` many-one reduces to `SubwordIneqAbsoluteness` in polynomial time (equivalently, a one-query reduction that negates the answer): for an instance $(SH_1, SH_2)$ put
$SH = SH_1 - SH_2$. The equation has no solution exactly when $|w|_{SH \times SH} > 0$ for every word $w$, that is, when
$SH \times SH - \lambda$ is nonnegative on all words. The construction maps letter-restricted instances over an alphabet to
letter-restricted instances over the same alphabet, so the nine-letter bound transfers. A good expansion links a page for the evaluation of products of subword histories ($|w|_{SH \times SH} = |w|_{SH}^2$).

## Sources

- S. Seki, "Absoluteness of subword inequality is undecidable", *Theoretical Computer Science* 418:116–120, 2012, doi:[10.1016/j.tcs.2011.10.017](https://doi.org/10.1016/j.tcs.2011.10.017). Numbering of the version read, arXiv:1108.2758v1: Lemma 1 (the reduction), Corollary 1 (undecidability) and Corollary 2 (nine letters, letter-restricted), and Section 1 (the open question of Mateescu, Salomaa and Yu and the decidability of equivalence, recalled there).
