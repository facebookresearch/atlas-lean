# Moving a bit block through a buffer

Let $a$, $t$, $b$ be pairwise distinct stacks of a
program $M$ with Boolean state, and let $l_1$, $l_2$, $l_3$ be labels such that $M$ runs at $l_1$
the bit-moving loop from $a$ to $t$ with decoder $d$ and encoder $g_t$, looping at $l_1$ and
exiting to $l_2$, and at $l_2$ the bit-moving loop from $t$ to $b$ with decoder $d_t$ and encoder
$g$, looping at $l_2$ and exiting to $l_3$, where $d_t$ decodes $g_t(y)$ to $y$ for every bit $y$.
Let $x = x_1 \cdots x_n$ be a bit list and $S$ stack contents in which $a$ holds a bit block for
$x$ under $d$ followed by a rest $A$ that ends a bit block under $d$, and $t$ is empty. Then for
every state $v$ there are a state $v'$ and stack contents $S'$ such that $M$ runs in exactly
$2n + 2$ steps from label $l_1$, state $v$ and stacks $S$ to label $l_3$, state $v'$ and stacks
$S'$, where $S'(a) = A$, $S'(t)$ is empty, $S'(b)$ is $g(x_1), \dots, g(x_n)$ (top first)
followed by $S(b)$, and $S'(k) = S(k)$ for every other stack $k$.
