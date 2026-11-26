# Two-destination bit transfer takes one step per bit plus one

Let $M$ be a multi-stack Turing machine with Boolean internal state whose statement at label self is the
[two-destination transfer](split-b.md) from stack $a$ to stacks $b$ and $c$ with decoder $d$, maps $g_b$, $g_c$
and labels self, next, where $a$, $b$, $c$ are pairwise distinct. Let $g_a$ map bits to symbols of stack $a$ with
$d(g_a(e)) = e$ for each bit $e$. Stack contents are listed from the top.

Let $p = p_1 \cdots p_m$ be a bit string, $t$ a string of symbols of stack $a$ that is empty or whose first symbol
is not decoded by $d$ to a bit, $v$ a Boolean and $S$ stack contents with $S_a = g_a(p_1) \cdots g_a(p_m)\, t$.
Then there are stack contents $S'$ such that $M$ goes from label self, internal state $v$ and stacks $S$ to label
next, internal state $0$ (false) and stacks $S'$ in exactly $m + 1$ steps, with $S'_a = t$,
$S'_b = g_b(p_m) \cdots g_b(p_1)\, S_b$, $S'_c = g_c(p_m) \cdots g_c(p_1)\, S_c$, and $S'_k = S_k$ for every
other stack $k$.
