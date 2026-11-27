# Autoreducibility and mitoticity

A set $A$ is **autoreducible** under a reducibility $\le_r$ if $A\le_r A$ via a reduction that, on input $x$, never queries $x$ itself. It is **($\le_r$-)mitotic** if it splits as $A=A_1\sqcup A_2$ with $A_1=A\cap S$ for some $S\in\mathsf{P}$ and $A\equiv_r A_1\equiv_r A_2$. Autoreducibility is monotone along the hierarchy of reducibilities (logspace many-one $\Rightarrow$ polynomial many-one $\Rightarrow$ 1-tt $\Rightarrow$ btt $\Rightarrow$ tt), closed under complement for many-one and truth-table variants, and every set in $\mathsf{P}$ is (0-tt) autoreducible.

## Depends on

- [Polynomial-time truth-table, bounded and Turing reductions](truth-table-reductions.md)

## Sources

- Klaus Ambos-Spies, "P-mitotic sets", Logic and Machines: Decision Problems and Complexity, 1984.
- Harry Buhrman, Lance Fortnow, Dieter van Melkebeek and Leen Torenvliet, "Separating Complexity Classes Using Autoreducibility", SIAM Journal on Computing 29(5), 2000.
