# Symbols left pushed by a situation are effective

Let $E$ be an encoding of a finite
multi-stack Turing machine $M$, and for each stack $k$ of $M$ let $s_k$ be the size of the
effective alphabet of stack $k$ in $E$ and $\mathrm{dec}_k(n)$, for $n < s_k$, its $n$-th
effective symbol. For every $i \in \mathbb{N}$, every stack $k$ of $M$ and every symbol $x$ of the
alphabet of stack $k$: if $x$ is among the symbols that the effect of situation $i$ leaves pushed
on stack $k$, then $x = \mathrm{dec}_k(n)$ for some $n < s_k$.
