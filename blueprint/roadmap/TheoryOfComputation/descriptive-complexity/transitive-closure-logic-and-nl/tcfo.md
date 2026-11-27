# Formulas of first-order logic with transitive closure

FO + TC formulas, with variables
and relation symbols indexed by natural numbers, are built from equations between two variables
and relation symbols applied to lists of variables by negation, conjunction, disjunction,
existential quantification (which binds variable $0$, de Bruijn style) and transitive closure
$\mathrm{TC}(\varphi; \bar u, \bar v)$ of a formula $\varphi$ applied to two lists $\bar u$,
$\bar v$ of variables. With $a = |\bar u| = |\bar v|$, the body $\varphi$ defines a step
relation on $a$-tuples: its variables $0, \dots, a - 1$ are the source tuple, $a, \dots, 2a - 1$
the target tuple, and each variable $j \ge 2a$ is outer variable $j - 2a$.
