# The laser method bound on omega from tensor values

Let $T$ be a tensor and $\tau \in [2/3, 1]$. By Schönhage's asymptotic sum inequality, $V_{\omega/3}(T) \le \underline{R}(T)$; consequently, if $V_\tau(T) > \underline{R}(T)$, then $\omega < 3\tau$. (The strict inequality is necessary: for the unit tensor $T = \langle 1, 1, 1\rangle$, $V_\tau(T) = 1 = \underline{R}(T)$ for every $\tau \in [2/3, 1]$.) For $T = \mathrm{CW}_q$, a lower bound on $V_\tau(\mathrm{CW}_q)$ is obtained from any probability distribution $\alpha$ on the six constituents: writing $H(\alpha_X)$ for the entropy of the induced marginal on $X$-blocks (and similarly for $Y, Z$),

$$
\log V_\tau(\mathrm{CW}_q) \ge \min\bigl(H(\alpha_X), H(\alpha_Y), H(\alpha_Z)\bigr) + \tau \sum_{c} \alpha(c) \log \mathrm{vol}(c),
$$

where $\mathrm{vol}(c) = nmk$ for a constituent $c \cong \langle n, m, k\rangle$, provided $\alpha$ is the only distribution on the constituents with its three marginals; in general the right side decreases by $\max_\beta H(\beta) - H(\alpha)$, the maximum over distributions $\beta$ with the same marginals as $\alpha$. Optimizing over $q$ and $\alpha$ gives $\omega < 2.38719$ (at $q = 6$); the second-level analysis of $\mathrm{CW}_q^{\otimes 2}$ gives the Coppersmith-Winograd bound $\omega < 2.375477$.

## Proof sketch

For any direct sum $\bigoplus_{i=1}^p \langle n_i, m_i, k_i\rangle$ of $p$ matrix multiplication tensors that is a restriction of $(T \otimes T^{r} \otimes T^{rr})^{\otimes N}$, border rank does not increase under restriction, is submultiplicative, and is preserved by the rotations $T^{r}, T^{rr}$, so the direct sum's border rank is at most $r = \underline{R}(T)^{3N}$. Whenever $r > p$, Schönhage's asymptotic sum inequality yields $\sum_{i=1}^p (n_i m_i k_i)^{\omega/3} \le r = \underline{R}(T)^{3N}$; taking $3N$-th roots and the supremum over such restrictions gives $V_{\omega/3}(T) \le \underline{R}(T)$, and since $V_\tau(T)$ is nondecreasing in $\tau$, $V_\tau(T) > \underline{R}(T)$ implies $\omega < 3\tau$. For the lower bound on the value, note that $\mathrm{CW}_q$ is invariant under rotation (renaming $x_i \mapsto y_i \mapsto z_i \mapsto x_i$ maps it to itself), so $(\mathrm{CW}_q \otimes \mathrm{CW}_q^{r} \otimes \mathrm{CW}_q^{rr})^{\otimes N}$ is isomorphic to $\mathrm{CW}_q^{\otimes 3N}$. Zero out $\mathrm{CW}_q^{\otimes 3N}$ to blocks of type $\alpha$ and apply the progression-free hashing, again by zeroing out, to obtain about $2^{3N \min H(\alpha_\cdot) - o(N)}$ independent block triples, each a product of constituents and hence a matrix multiplication tensor of volume $\prod_c \mathrm{vol}(c)^{3N\alpha(c)}$; zeroing outs are restrictions, so taking $3N$-th roots gives the stated bound.

## Depends on

- [The Coppersmith–Winograd tensor](cw-tensor.md)
- [The value of a tensor in the laser method](tensor-value.md)

## Proof depends on

- [Schönhage's asymptotic sum inequality](asymptotic-sum-inequality.md)
- [Coppersmith–Winograd hashing with progression-free sets](salem-spencer-hashing.md)
- [The Coppersmith–Winograd tensor has border rank q+2](cw-border-rank.md)
- [Coppersmith–Winograd 1990 bound on the square exponent](../matrix-multiplication-exponent/coppersmith-winograd1990-upper.md)

## Sources

- D. Coppersmith, S. Winograd, "Matrix multiplication via arithmetic progressions", Journal of Symbolic Computation 9 (1990) 251-280.
- V. Strassen, "Relative bilinear complexity and matrix multiplication", Journal für die reine und angewandte Mathematik 375/376 (1987) 406-443.
