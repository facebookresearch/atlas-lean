# Finitely many formulas of bounded quantifier rank up to equivalence

For a vocabulary with finitely many relation symbols and no function symbols, and for all $k, n \in \mathbb{N}$, there are only finitely many formulas in $k$ free variables of quantifier rank at most $n$ up to logical equivalence. Consequently $\equiv_n$ has finitely many equivalence classes on $k$-pointed structures, each class is defined by a single formula of quantifier rank $n$, and every sentence of rank $n$ is equivalent to a finite disjunction of such class-defining sentences.

## Proof sketch

Induction on $n$, simultaneously for all $k$: rank-$0$ formulas in $k$ variables are Boolean combinations of the finitely many atomic formulas in those variables; a rank-$(n+1)$ formula in $k$ variables is a Boolean combination of atomic formulas and formulas $\exists x_{k+1}\psi$ with $\psi$ of rank at most $n$ in $k+1$ variables, of which there are finitely many up to equivalence.

## Depends on

- [Quantifier rank and rank-$n$ equivalence](quantifier-rank.md)

## Sources

- L. Libkin, Elements of Finite Model Theory, Springer, 2004.
- H.-D. Ebbinghaus and J. Flum, Finite Model Theory, 2nd ed., Springer, 1999.
