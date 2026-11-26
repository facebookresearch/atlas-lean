# TQBF as a decision problem

The TQBF decision problem accepts a bitstring $x$ exactly when
$x$ decodes, under the canonical bitstring encoding, to a pair $(Q, \varphi)$, where $Q$ is a
quantifier prefix, a list of $m$ pairs $(e_1, v_1), \dots, (e_m, v_m)$ of a flag $e_i$ (true for
$\exists$, false for $\forall$) and a variable $v_i \in \mathbb{N}$, and $\varphi$ is a CNF
formula, such that $v_1, \dots, v_m$ are $0, 1, \dots, m - 1$ in some order, every variable
occurring in $\varphi$ is less than $m$, and the quantified formula with prefix $Q$ and matrix
$\varphi$ holds under the assignment that sends every variable to false.
