# The capped filter fails on a clause with too many literals

Let $n \le 3$, let
$\ell_1, \dots, \ell_k$ be literals (pairs of a variable index and a polarity) with $3 < n + k$,
and let $w$ be the concatenation of the stack tokens of $\ell_1, \dots, \ell_k$. For all lists of
symbols $R$ and $U$ and every internal state $v$, the capped filter program, started at the
walking label for $n$ literals with internal state $v$, token stack $wR$ (top first) and side
stack $U$, reaches the failure label, with some internal state and some stacks, in at most $|w|$
steps.
