# Parity is not first-order definable even with arbitrary numerical predicates

Let $L$ be a finite relational vocabulary with a unary symbol $P$, and for each $n$ fix an arbitrary interpretation $N_n$ of the other symbols on the universe $\{1,\dots,n\}$ (for example a linear order and $\mathrm{BIT}$, or any relations at all, chosen separately for each $n$). Then no first-order sentence $\varphi$ of $L$ has the property that for all large $n$ and all $S\subseteq\{1,\dots,n\}$, the expansion of $N_n$ interpreting $P$ as $S$ satisfies $\varphi$ iff $|S|$ is even. In particular parity is not in $\mathrm{FO}[\mathrm{Arb}]$, and is not definable with the canonical constants $0,1,\max$, order and $\mathrm{BIT}$.

## Proof sketch

A definition would give, by first-order model checking, constant-depth polynomial-size unbounded fan-in circuits for parity of $|S|$ (the numerical relations become constants), contradicting that parity is not in $\mathsf{AC}^0$.

## Depends on

- [Logics on finite structures as query languages](../../../descriptive-complexity/finite-model-theory/logics-on-finite-structures-as-query-languages.md)

## Proof depends on

- [First-order model checking in constant depth](first-order-model-checking-in-ac0.md)
- [Parity is not in AC0](../../lower-bounds-for-ac0-circuits/parity-not-in-ac0.md)

## Sources

- Merrick Furst, James B. Saxe, Michael Sipser, "Parity, Circuits, and the Polynomial-Time Hierarchy", Mathematical Systems Theory 17(1), 1984.
- Miklós Ajtai, "Σ¹₁-Formulae on Finite Structures", Annals of Pure and Applied Logic 24(1), 1983.
- Neil Immerman, "Descriptive Complexity", Springer, 1999.
