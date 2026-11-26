# Catalytic equality test by four alternating visits

Let $R$ be a commutative ring and let $x,y\in R^{\ell}$ be accessible only one at a time. There is a procedure using a borrowed register $r\in R^{\ell}$ with arbitrary content $S$ and an accumulator $z\in R$ that visits $x,y,x,y$ in this order and adds $c\cdot\langle x-y,x-y\rangle=c\sum_i(x_i-y_i)^2$ to $z$ while restoring $r$ to $S$, for every initial $S$ and $z$: visit $x$ (mask $r\leftarrow r+x$, add $c\langle x,x\rangle$), visit $y$ (add $c(\langle y,y\rangle-2\langle r,y\rangle)$), visit $x$ (unmask $r\leftarrow r-x$), visit $y$ (add $2c\langle r,y\rangle$). Running it with $c=1$, observing whether $z$ changed, and running it with $c=-1$ decides $x=y$ whenever squared distance detects equality (e.g. over $\mathbb{Z}$, or over $\mathbb{Z}/2^{k}$ when $\ell(2^{q}-1)^2<2^{k}$ for $q$-bit digits) and restores both the register and the accumulator.

## Proof sketch

The two inner products with $y$ see $S+x$ and $S$, so the unknown content $S$ cancels and $-2c\langle x,y\rangle$ remains; adding the other terms gives $c\|x-y\|^2$. The call with $-c$ subtracts exactly the same amount.

## Depends on

- [Catalytic space computation](catalytic-space.md)

## Sources

- OpenAI, "Exact Derandomization of Logarithmic Space: L = RL = BPL", Preprint, 2026.
- Harry Buhrman et al., "Computing with a Full Memory: Catalytic Space", Proceedings of the 46th Annual ACM Symposium on Theory of Computing, 2014.
