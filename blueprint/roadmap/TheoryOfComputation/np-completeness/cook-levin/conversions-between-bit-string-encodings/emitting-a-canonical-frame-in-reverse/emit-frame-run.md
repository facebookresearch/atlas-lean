# Frame emitter takes one step per payload bit plus one

Let $M$ be a multi-stack Turing machine with Boolean internal state whose statement at label self is the
[frame-emitting statement](emit-frame.md) from stack $a$ to stack $b$ with decoder $d$, map $g$ and labels self,
next, where $a \ne b$. Let $g_a$ map bits to symbols of stack $a$ with $d(g_a(e)) = e$ for each bit $e$. Stack
contents are listed from the top.

Let $p = p_1 \cdots p_m$ be a bit string, $t$ a string of symbols of stack $a$ that is empty or whose first symbol
is not decoded by $d$ to a bit, $v$ a Boolean and $S$ stack contents with $S_a = g_a(p_1) \cdots g_a(p_m)\, t$.
Then there are stack contents $S'$ such that $M$ goes from label self, internal state $v$ and stacks $S$ to label
next, internal state $0$ (false) and stacks $S'$ in exactly $m + 1$ steps, with $S'_a = t$, $S'_b$ equal to $g$
applied to the framed form $1 p_1 \cdots 1 p_m 0$ of $p$, reversed, followed by $S_b$, and $S'_k = S_k$ for every
other stack $k$.
