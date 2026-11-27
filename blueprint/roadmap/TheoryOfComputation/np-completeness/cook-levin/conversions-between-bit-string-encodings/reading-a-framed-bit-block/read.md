# Machine step reading one framed payload pair

Write $1$ for true and $0$ for false. The *framed form* of a bit string $p = p_1 \cdots p_m$ is
$1 p_1 1 p_2 \cdots 1 p_m 0$: every payload bit is preceded by a $1$ and the block ends with a $0$.

Consider a multi-stack Turing machine with labels $\Lambda$, Boolean internal state and a stack alphabet
$\Gamma_k$ for each stack $k$. Fix two stacks $a$ and $b$, a partial decoder $d$ sending each symbol of $\Gamma_a$
to a bit or to nothing, a map $g$ from bits to $\Gamma_b$, and three labels self, good and bad. The framed-pair
reading statement does the following:

1. If stack $a$ is empty or its top symbol is not decoded by $d$ to a bit, go to bad.
2. Otherwise pop that symbol and set the internal state to its bit $c$. If $c = 0$, go to good.
3. If $c = 1$: if stack $a$ is now empty or its top symbol is not decoded to a bit, go to bad; otherwise pop
   that symbol, set the internal state to its bit $c'$, push $g(c')$ onto stack $b$ and go to self.

When $a \ne b$, executing it repeatedly at label self reads one framed block from stack $a$ and pushes its payload, reversed,
onto stack $b$.
