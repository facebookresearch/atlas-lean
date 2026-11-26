# Moving a bit block through a buffer

Let $M$ be a multi-stack machine program with stack set $K$ (with decidable equality), stack
alphabets $(\Gamma_k)_{k \in K}$, label set $\Lambda$ and the bits as internal states, and let $a$,
$t$, $b$ be pairwise distinct stacks. Let $d$ be a partial map from $\Gamma_a$ to the bits (a
decoder), $g_t$ a map from the bits to $\Gamma_t$, $d_t$ a partial map from $\Gamma_t$ to the bits
such that $d_t(g_t(y))$ is defined and equal to $y$ for every bit $y$, and $g$ a map from the bits
to $\Gamma_b$. Let $l_1$, $l_2$, $l_3$ be labels such that the statement of $M$ at $l_1$ is the
bit-moving loop from $a$ to $t$ with decoder $d$ and encoder $g_t$, looping at $l_1$ and exiting
to $l_2$, and the statement at $l_2$ is the bit-moving loop from $t$ to $b$ with decoder $d_t$ and
encoder $g$, looping at $l_2$ and exiting to $l_3$. (In one step, the bit-moving loop from a stack
$u$ to a stack $u'$ either pops the top symbol of $u$, which decodes to a bit $y$, pushes the
encoding of $y$ onto $u'$ and returns to its own label, or, when $u$ is empty or its top symbol
decodes to no bit, goes to its exit label.)

Let $x = x_1 \cdots x_n$ be a bit list and $S$ stack contents such that $S(t)$ is empty and
$S(a)$ consists of symbols $s_1, \dots, s_n$ (top first) followed by a rest $A$, where $d(s_i)$ is
defined and equal to $x_i$ for every $i$, and $A$ is empty or its top symbol has no value under
$d$. Then for every bit $v$ there are a bit $v'$ and stack contents $S'$ such that $M$ runs in
exactly $2n + 2$ steps from label $l_1$, state $v$ and stacks $S$ to label $l_3$, state $v'$ and
stacks $S'$, where $S'(a) = A$, $S'(t)$ is empty, $S'(b)$ is $g(x_1), \dots, g(x_n)$ (top first)
followed by $S(b)$, and $S'(k) = S(k)$ for every other stack $k$.
