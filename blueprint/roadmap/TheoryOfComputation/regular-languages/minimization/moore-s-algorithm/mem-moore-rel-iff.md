# Correctness of Moore's refinement

For a DFA $M$ over a finite alphabet with finitely
many states, two states $p$ and $q$ of $M$ are related by Moore's relation if and only if they
have the same continuation language: for every word $w$, $M$ started at $p$ accepts $w$ exactly
when $M$ started at $q$ accepts $w$.
