# Quadratic equations with boundedly many variables are in P

For every fixed bound on the number of variables, satisfiability of quadratic word equations is decidable in polynomial time, because minimal solutions are then polynomially long. The degree of the polynomial depends on the bound.

Let $V \ge 0$ be a fixed integer. The problem of deciding whether a given quadratic word equation $\alpha = \beta$ over an alphabet of constants with at least two letters (given with the input), with at most $V$ distinct variables, has a solution (variables mapped to possibly empty words) can be solved in time polynomial in the size of the input. The polynomial depends on $V$; no algorithm uniformly polynomial in $V$ is claimed.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)
- [Polynomial time on multi-tape machines](../../complexity-classes/time-and-space-classes-on-multi-tape-machines/p.md)
- [Solution of a word equation](../string-constraints-and-word-equations/ordinary-word-equations/satisfies.md)

## Proof depends on

None.

## Expansion

A solution $h$ is *minimal* if no solution $h'$ has $|h'(\alpha)| < |h(\alpha)|$; as in the source, erasing solutions are included, so this is not the [length-minimality](../word-equation-algorithms/minimal-solutions/length-minimal-solution.md) among nonerasing solutions. The source derives the result from its bound on chains. Let $V_2 \le V$ be the number of variables occurring twice. If the equation has a solution, it has one in which every chain of equivalent positions has length at most $2^{2^{O(V_2^4)}}$ (Proposition 16, which uses the chain-shortening lemma: a chain containing a repeated "similar" segment can be shortened, giving a shorter solution). Consequently every minimal solution $h$ satisfies $|h(\alpha)| \le |\alpha\beta| \cdot 2^{2^{O(V_2^4)}}$ (the second sentence of Proposition 16), so for fixed $V$ some solution has length $O(|\alpha\beta|)$, with a constant depending on $V$. With at most $V$ variables, one enumerates the polynomially many tuples of lengths $(|h(x)|)_x$ bounded in this way. For each tuple one decides by *filling the positions* whether a solution with these lengths exists: identify the positions of the two sides that must carry the same letter, through the occurrences of the variables, and check that no class contains two different constants. Each test takes polynomial time. The chain-shortening lemma and the position-filling test are internal to the source.

## Sources

- Joel D. Day, Florin Manea and Dirk Nowotka, "Upper Bounds on the Length of Minimal Solutions to Certain Quadratic Word Equations", 44th International Symposium on Mathematical Foundations of Computer Science (MFCS 2019), LIPIcs 138, Article 44, pp. 44:1–44:15, 2019, <https://doi.org/10.4230/LIPIcs.MFCS.2019.44>, Section 3 (chains representation, Lemma 11, the method of filling the positions), Proposition 16 (chain bounds in terms of the number of twice-occurring variables), and Proposition 17 (polynomial time for a constant number of variables) with the discussion preceding it.
