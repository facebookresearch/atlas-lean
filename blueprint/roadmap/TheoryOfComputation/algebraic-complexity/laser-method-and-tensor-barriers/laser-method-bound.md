# The laser method bound on omega from tensor values

Let $T$ be a tensor and $\tau \in [2/3, 1]$. If $V_\tau(T) \ge \underline{R}(T)$, then $\omega \le 3\tau$. For $T = \mathrm{CW}_q$, a lower bound on $V_\tau(\mathrm{CW}_q)$ is obtained from any probability distribution $\alpha$ on the six constituents: writing $H(\alpha_X)$ for the entropy of the induced marginal on $X$-blocks (and similarly for $Y, Z$),

$$
\log V_\tau(\mathrm{CW}_q) \ge \min\bigl(H(\alpha_X), H(\alpha_Y), H(\alpha_Z)\bigr) + \tau \sum_{c} \alpha(c) \log \mathrm{vol}(c),
$$

where $\mathrm{vol}(c) = nmk$ for a constituent $c \cong \langle n, m, k\rangle$, under the condition that the marginals determine $\alpha$ (otherwise a penalty term appears). Optimizing over $q$ and $\alpha$ gives $\omega < 2.3755$, the Coppersmith-Winograd bound.

## Proof sketch

The first statement is the asymptotic sum inequality applied to the direct sums witnessing $V_\tau(T)$ together with submultiplicativity of border rank. For the lower bound on the value, restrict $T^{\otimes N}$ to blocks of type $\alpha$, apply the progression-free hashing to obtain about $2^{N \min H(\alpha_\cdot) - o(N)}$ independent block triples, each a product of constituents and hence a matrix multiplication tensor of volume $\prod_c \mathrm{vol}(c)^{N\alpha(c)}$.

## Depends on

- [Coppersmith–Winograd hashing with progression-free sets](salem-spencer-hashing.md)
- [The Coppersmith–Winograd tensor has border rank q+2](cw-border-rank.md)
- [Coppersmith–Winograd 1990 bound on the square exponent](../matrix-multiplication-exponent/coppersmith-winograd1990-upper.md)

## Proof depends on

- [Coppersmith–Winograd hashing with progression-free sets](salem-spencer-hashing.md)
- [The Coppersmith–Winograd tensor has border rank q+2](cw-border-rank.md)
- [Coppersmith–Winograd 1990 bound on the square exponent](../matrix-multiplication-exponent/coppersmith-winograd1990-upper.md)

## Sources

- D. Coppersmith, S. Winograd, "Matrix multiplication via arithmetic progressions", Journal of Symbolic Computation 9 (1990) 251-280.
- V. Strassen, "Relative bilinear complexity and matrix multiplication", Journal für die reine und angewandte Mathematik 375/376 (1987) 406-443.
