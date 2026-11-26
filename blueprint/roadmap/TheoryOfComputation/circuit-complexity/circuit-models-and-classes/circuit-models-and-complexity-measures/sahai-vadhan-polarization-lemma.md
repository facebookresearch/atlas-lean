# Sahai–Vadhan polarization lemma for circuit samplers

Let $C_0,C_1$ be circuit samplers with $n$ inputs and $m$ outputs, and let $0\le\beta<\alpha^2\le 1$. There is a polynomial-time transformation that, given $C_0,C_1$ and a security parameter $k$ in unary, outputs samplers $D_0,D_1$ of size polynomial in $|C_0|+|C_1|+k$ such that:

- if $\Delta(D_{C_0},D_{C_1})\ge\alpha$ then $\Delta(D_{D_0},D_{D_1})\ge 1-2^{-k}$;
- if $\Delta(D_{C_0},D_{C_1})\le\beta$ then $\Delta(D_{D_0},D_{D_1})\le 2^{-k}$.

The construction alternates the *XOR lemma* step (run $C_{c\oplus r_1\oplus\cdots\oplus r_j}$ and $C_{r_i}$ on independent blocks, which maps distance $\delta$ to $\delta^{j}$) with direct products (which push distance towards $1$).

## Proof sketch

For the XOR construction on $j$ coordinates the distance of the two output distributions is exactly $\delta^j$; for the $k$-fold direct product the distance $\delta$ becomes at least $1-2e^{-k\delta^2/2}$ and at most $k\delta$. Alternating the two operations with suitable parameters separates the cases $\delta\ge\alpha$ and $\delta\le\beta$ when $\beta<\alpha^2$.

## Depends on

- [Circuit samplers and output distributions](circuit-samplers-and-output-distributions.md)

## Sources

- Amit Sahai, Salil Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM, 2003.
