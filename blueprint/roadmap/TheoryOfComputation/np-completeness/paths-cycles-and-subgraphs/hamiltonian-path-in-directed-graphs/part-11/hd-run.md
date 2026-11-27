# Running the head-or-edge check

Let $es$ be an edge list, $s, t, n, c, b, a$ numbers and
$q$ a list of vertices, and say the check passes when $a = s$ in case $c = 0$, and
$(b, a) \in es$ in case $c \neq 0$. Started at the head-or-edge dispatch, in any internal state,
on the stack layout during the step on vertex $a$ for $es, s, t, n, c, b, a, q$, the verifier
reaches within $3a + 4\ell + 7$ steps, where $\ell$ is the number of bits of $es$, the repeat
scan if the check passes and the reject label otherwise, in some internal state and with some
stacks; if the check passes, these stacks are the ones it started on.
