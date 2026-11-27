# Bit-block copy keeps the order and restores source and scratch

Let $M$ be a multi-stack Turing machine with Boolean internal state and let $a$, $b$, $t$ be pairwise distinct
stacks, with partial decoders $d_a$, $d_t$ (symbols of $a$, resp. $t$, to a bit or nothing) and maps $g_a$, $g_b$,
$g_t$ from bits to symbols of $a$, $b$, $t$ such that $d_a(g_a(e)) = e$ and $d_t(g_t(e)) = e$ for each bit $e$.
Suppose that at label first $M$ runs the bit-moving loop from $a$ to $t$ (while the top of $a$ is decoded by $d_a$
to a bit $e$, pop it, push $g_t(e)$ onto $t$ and stay at first; otherwise go to second), and that at label second
it runs the [two-destination transfer](split-b.md) from $t$ to $a$ and $b$ with decoder $d_t$, maps $g_a$, $g_b$
and labels second, next. Stack contents are listed from the top.

Let $p = p_1 \cdots p_m$ be a bit string, $u$ a string of symbols of $a$, $v$ a Boolean and $S$ stack contents with
$S_a = g_a(p_1) \cdots g_a(p_m)\, u$, where $u$ is empty or its first symbol is not decoded by $d_a$ to a bit, and
$S_t$ is empty or its first symbol is not decoded by $d_t$ to a bit. Then there are stack contents $S'$ such that
$M$ goes from label first, internal state $v$ and stacks $S$ to label next, internal state $0$ (false) and stacks
$S'$ in exactly $2m + 2$ steps, with $S'_a = S_a$, $S'_t = S_t$, $S'_b = g_b(p_1) \cdots g_b(p_m)\, S_b$ (the
block in its original order on top of the old contents of $b$), and $S'_k = S_k$ for every other stack $k$.
