# Restricting a statement of the code evaluator to the wrapped machine

Let $\mathrm{tr}$ be
Mathlib's four-stack machine that evaluates partial recursive codes, and let $S$ be the support
of a code $c$. A statement $q$ of $\mathrm{tr}$ all of whose jump targets lie in $S$ becomes a
statement of the wrapped machine of $c$ with the same structure: each push, peek and pop acts on
the same stack of $\mathrm{tr}$ inside the wrapped machine with the same function, loads and
branches are kept, each jump goes to the same label of $\mathrm{tr}$, now read as an element of
$S$, and halting becomes a jump to the first post-phase label.
