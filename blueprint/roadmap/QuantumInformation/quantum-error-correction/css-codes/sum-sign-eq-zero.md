# Character sums over a binary linear code

Let $C \subseteq \mathbb{F}_2^n$ be a linear code and $u \in \mathbb{F}_2^n$. If some $c \in C$ has
$c \cdot u \ne 0$, then

$$\sum_{v \in C} (-1)^{v \cdot u} = 0.$$

Translating by $c$ is a bijection of $C$ that flips every sign, so the sum $S$ satisfies
$S = -S$. Calderbank and Shor use this to show that distinct codewords are orthogonal: the sum
vanishes "unless $vMw = 0$ for all $v$".

## Sources

- A. R. Calderbank and P. W. Shor, *Good quantum error-correcting codes exist*, Phys. Rev. A 54 (1996), 1098–1105, arXiv:quant-ph/9512032, Section III, after equation (2).
