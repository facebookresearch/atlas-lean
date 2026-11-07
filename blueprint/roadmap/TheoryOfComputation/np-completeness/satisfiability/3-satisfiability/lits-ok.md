# The filter walks a clause's literals within the cap

Let $c$ be a Boolean (whether the
filter is capped), let $\ell_1, \dots, \ell_k$ be literals (pairs of a variable index and a
polarity), let $n$ be a natural number with $c$ false or $n + k \le 3$, and let $w$ be the
concatenation of the stack tokens of $\ell_1, \dots, \ell_k$. For all lists of symbols $R$ and $U$
and every internal state $v$, the filter program with cap $c$, started at the walking label for $n$
literals with internal state $v$, token stack $wR$ (top first) and side stack $U$, reaches in
exactly $|w|$ steps the walking label for $n + k$ literals, with some internal state, token stack
$R$ and side stack $w^{\mathrm{rev}} U$, where $w^{\mathrm{rev}}$ is $w$ reversed.
