# The 3-COLOR emitter processes one clause

Let $C$ be a CNF clause, $T_C$ its tokens as
they lie on the token stack, $s$ a construction state that satisfies the size invariant after
$\tau$ tokens, and $L$ a bound with $\tau + |T_C| \le L$. Let $Y$ be a list of symbols that is
empty or starts with the clause marker, and $o_0$ a list of bits. For a construction state $t$
and a symbol list $X$, write $q(t, X)$ for the quiescent state encoding $t$ with token stack $X$,
output stack holding the bits of the edges emitted in $t$ above $o_0$, OR output $0$ and
first-literal flag $0$. Then for every Boolean $v$ there is a Boolean $v'$ such that the emitter
goes in at most $|T_C| \cdot (400 (L + 1)^2 + 1)$ steps from label $\mathsf{cls}$ with internal
state $v$ and the stacks of $q(s, T_C Y)$ to label $\mathsf{cls}$ with internal state $v'$ and
the stacks of $q(s_C, Y)$, where $T_C Y$ is $T_C$ on top of $Y$ and $s_C$ is the construction
state after clause $C$ is processed from $s$.
