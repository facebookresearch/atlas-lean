# Faithful clauses with a literal agreeing with the real run are satisfied

Let $M$ be a
finite stack machine with encoding data $E$, let $s$ be an input of $M$, let
$T, H \in \mathbb{N}$, and let $V$ be the number of variables of the layout of $E$ for $T$ and
$H$. Let $\ell$ be a list of literals that is faithful for $V$, and let $(p, b) \in \ell$ be a
literal such that $b$ is true exactly when $p$ is a run literal of $s$ at height $H$. Then the
dense clause over $V$ variables built from $\ell$ is satisfied by the run assignment of $s$ for
$T$ and $H$, which is true exactly on the run literals.
