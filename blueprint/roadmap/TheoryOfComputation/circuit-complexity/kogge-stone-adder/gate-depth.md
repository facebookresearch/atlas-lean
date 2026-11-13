# Gate-depth formula for the ripple-carry adder

Let $c(i)$ be the carry depth of bit $i$:
$c(0) = 0$ and $c(i) = 2i + 1$ for $i \ge 1$. The formula assigns to gate $j$ of the ripple-carry
adder, for every $j \in \mathbb{N}$, the depth $1$ when $j \bmod 5$ is $0$ or $2$, the depth
$\max(1, c(\lfloor j/5 \rfloor)) + 1$ when $j \bmod 5$ is $1$ or $3$, and the depth
$c(\lfloor j/5 \rfloor + 1)$ when $j \bmod 5 = 4$.
