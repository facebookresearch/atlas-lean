# Reading a complete framed block

Let $M$ be a multi-stack Turing machine with Boolean internal state whose statement at label self is the
[framed-pair reading step](read.md) from stack $a$ to stack $b$ with decoder $d$, symbol map $g$ and labels self,
good, bad, where $a \ne b$. Let $g_a$ map bits to symbols of stack $a$ with $d(g_a(c)) = c$ for each bit $c$.

Stack contents are listed from the top. Let $p$ be a bit string, $t$ a string of symbols of stack $a$, $v$ a Boolean and $S$ stack contents such that
stack $a$ holds $g_a$ applied letter by letter to the framed form $1 p_1 \cdots 1 p_m 0$ of $p$, followed by
$t$. Then there are stack contents $S'$ such that $M$ goes from label self, internal state $v$ and stacks $S$ to
label good, internal state $0$ (false) and stacks $S'$ in exactly $|p| + 1$ steps, where

- $S'_a = t$,
- $S'_b = g(p_m) \cdots g(p_1)\, S_b$ (the image of $p$ under $g$, reversed, on top of the old contents of $b$),
- $S'_k = S_k$ for every stack $k \ne a, b$.
