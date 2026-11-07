# Output loop for the pair bits of the KG-map machine

Let $m$ be a mode and $y$ and $o$
lists of bits. Consider a configuration of the KG-map machine $M_m$ at the label output pair
bits, with any internal bit, in which stack $Y$ holds the symbols $\mathrm{val}(b)$ for the bits
$b$ of $y$, the first bit of $y$ on top, and the output stack $O$ holds $o$. Then in exactly
$|y| + 1$ steps $M_m$ reaches the label output $n$ with $O$ equal, top first, to false, then the
reverse of $\beta_m(y)$, then $o$, where $\beta_m$ negates every bit for flip and leaves the
bits unchanged for vc; every stack other than $Y$ and $O$ is unchanged.
