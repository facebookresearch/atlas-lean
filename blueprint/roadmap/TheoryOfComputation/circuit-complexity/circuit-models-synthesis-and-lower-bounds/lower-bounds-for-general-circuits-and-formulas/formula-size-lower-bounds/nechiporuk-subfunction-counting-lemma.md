# Nechiporuk's subfunction counting lemma

Let $Y$ be a set of variables. A formula over the full binary basis $B_2$ whose leaves include exactly $\ell\ge1$ leaves labelled by variables of $Y$ computes at most $16^\ell$ distinct subfunctions on $Y$, where a *subfunction on $Y$* is obtained by fixing all variables outside $Y$ to constants.

## Proof sketch

Let $T$ be the subtree formed by the $\ell$ leaves labelled by variables of $Y$ and their paths to the output, and let $W$ be its nodes of in-degree two, so $|W|=\ell-1$. Cut $T$ into paths that start at a leaf or a node of $W$, end at a node of $W$ or the root, and have no node of $W$ inside; there are at most $2(|W|+1)=2\ell$ of them. After fixing the variables outside $Y$, the function on the last edge of such a path is $0$, $1$, $h$ or $\neg h$, where $h$ is computed at its first node, so there are at most $4^{2\ell}=16^\ell$ subfunctions.

Derived here (sharper): every unary function on an edge into a node of $W$ can be absorbed into that node's two-argument Boolean function (16 choices), leaving only the unary function above the topmost node (4 choices); this gives at most $4\cdot 16^{\ell-1}=16^\ell/4$ subfunctions. If $\ell=0$ the subfunctions are constants, so there are at most two.

## Depends on

- [Circuit complexity, binary cost and formula leaf size](../../circuit-models-and-classes/circuit-models-and-complexity-measures/circuit-complexity-and-formula-leaf-size.md)

## Sources

- E. I. Nechiporuk, "On a Boolean function", Soviet Mathematics Doklady 7(4), 999–1000, 1966.
- Ingo Wegener, "The Complexity of Boolean Functions", Wiley-Teubner, 1987 (Chapter 8, Section 7, proof of Theorem 7.1, inequalities (7.2)–(7.4), pp. 253–254).
- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
