# Quadratic equations with infinitely many solutions have unbounded exponent

A quadratic word equation over a free semigroup either has finitely many solutions or has solutions containing arbitrarily high powers of nonempty words. The free-semigroup convention matters: variables must be mapped to nonempty words.

Let $\Sigma$ be a finite alphabet of constants and $\mathcal X$ a finite set of variables. A word equation $U = V$ with $U, V \in (\Sigma \cup \mathcal X)^+$ is considered over the free semigroup $\Sigma^+$: a solution is a map $\sigma : \mathcal X \to \Sigma^+$ (no variable is mapped to the empty word) with $\sigma(U) = \sigma(V)$. The exponent of periodicity of a word $w$, $\exp(w)$, is the largest $e$ such that $p^e$ is a factor of $w$ for some nonempty word $p$ ($\exp(w) = 0$ iff $w$ is empty); for a solution, $\exp(\sigma) = \max_{X \in \mathcal X} \exp(\sigma(X))$, measured on the images of the individual variables, and $\exp(U = V) = \sup_\sigma \exp(\sigma) \in \mathbb N \cup \{\infty\}$, the supremum over **all** solutions, not only shortest ones. By convention the maximum and the supremum of the empty family are $0$; an equation without variables has at most one solution (the empty assignment), so the statement below holds trivially for it.

If $U = V$ is quadratic (every variable occurs at most twice in $UV$), then it has only finitely many solutions or $\exp(U = V) = \infty$.

## Depends on

- [Quadratic, regular and regular-ordered word equations](restricted-classes-of-word-equations.md)

## Proof depends on

- [Length-directed Levi's lemma](../string-constraints-and-word-equations/levi-of-le.md)

## Expansion

The converse direction is trivial: $\exp(U = V) = \infty$ forces infinitely many solutions. For the stated direction, assume infinitely many solutions and argue by induction, primarily on the number of variables and secondarily on $|UV|$. A twice-occurring variable is *balanced* if it occurs once on each side. Simple cases: if some variable does not occur in $UV$, vary its value over $a^n$; if both sides begin with the same constant or the same variable, cancel it; if one side begins with a balanced variable $X$ and the other is $V_1 X V_2$ with $V_1$ nonempty, then from a solution $\sigma$ one gets solutions $\sigma_n(X) = \sigma(V_1)^n \sigma(X)$ with exponent at least $n$; if one side is a single variable, substitute it away. Otherwise one applies substitutions $\tau$ ($X \mapsto a$, $X \mapsto aX$, $X \mapsto Y$, $X \mapsto YX$) chosen so that the new equation still has infinitely many solutions; each of its solutions $\sigma'$ yields the solution $\sigma' \tau$ of the original equation with $\exp(\sigma'\tau) \ge \exp(\sigma')$. Once-occurring variables can be treated like constants, and in the remaining case of two unbalanced leading variables the substitution $X \mapsto YX$ makes $Y$ balanced for good, so this case occurs at most $|\mathcal X|$ times in a row and the process reaches a simple case. The conjecture that every word equation with infinitely many solutions has unbounded exponent of periodicity is open in general; it is known for two-variable equations, and the source extends the quadratic case to regular constraints recognised by finite semigroups in the variety DLG and in its left-right dual; nothing is claimed here for arbitrary regular constraints.

## Sources

- Volker Diekert, Silas Natterer and Alexander Thumm, "Quadratic word equations with regular constraints and the exponent of periodicity", *Semigroup Forum*, 2026 (accepted 4 August 2026), <https://doi.org/10.1007/s00233-026-10675-x> (open access), Section 3 (word equations over free semigroups, solutions in $\Sigma^+$), Section 3.2 (exponent of periodicity), Proposition 11 (the trivial semigroup is nice for quadratic equations, that is, the statement above) with its proof in Section 5, Theorem 1 (constraints in DLG), Proposition 5 in Section 3.3 (two-variable equations); arXiv:2511.08208v3 (Proposition labelled prop:trivial, same statement).
