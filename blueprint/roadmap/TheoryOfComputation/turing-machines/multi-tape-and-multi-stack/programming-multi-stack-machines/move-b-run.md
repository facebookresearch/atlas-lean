# Running the bit-moving loop

Let $a \ne b$ be stacks of a program $M$ whose state carries
a flag bit, $d$ a decoder reading each symbol of $a$ as a bit or a marker, $g$ an encoder from bits
to symbols of $b$, and $\mathit{self}$, $\mathit{next}$ labels such that $M$ runs at
$\mathit{self}$ the bit-moving loop from $a$ to $b$ with decoder $d$ and encoder $g$, looping at
$\mathit{self}$ and exiting to $\mathit{next}$. Let $p = p_1 \cdots p_n$ be a bit list and $S$
stack contents in which $a$ holds a bit block for $p$ under $d$ followed by a rest $A$ that ends a
bit block under $d$. Then for every state $v$ there are a state $v'$ and stack contents $S'$ such
that $M$ runs in exactly $n + 1$ steps from label $\mathit{self}$, state $v$ and stacks $S$ to
label $\mathit{next}$, state $v'$ and stacks $S'$, where $S'(a) = A$, $S'(b)$ is
$g(p_n), \dots, g(p_1)$ (top first) followed by $S(b)$, and $S'(k) = S(k)$ for every other stack
$k$.
