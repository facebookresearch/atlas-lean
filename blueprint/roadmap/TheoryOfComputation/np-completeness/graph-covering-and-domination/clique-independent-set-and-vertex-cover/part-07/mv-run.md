# Moving the pair bits onto stack $Y$

Fix a mode $m$ of the CLIQUE/VERTEX-COVER
reduction machine, a list of bits $r$ and a list of symbols $y$. Start the machine for $m$ at the
label for moving the pair bits, with any internal state and any stacks such that stack $X$ holds
$r$ as the symbols $\mathrm{bit}(b)$ and stack $Y$ holds $y$. Then after exactly $|r| + 1$ steps
it is at the label that follows moving the pair bits in mode $m$, with some internal state and
stacks in which $Y$ holds the symbols $\mathrm{val}(b)$ for the bits $b$ of $r$, in reverse
order, on top of $y$, and every stack other than $X$ and $Y$ is unchanged.
