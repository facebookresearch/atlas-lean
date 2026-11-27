# Paturi–Simon: unbounded-error complexity equals log sign-rank

For all finite sets $X,Y$ and every $f:X\times Y\to\{0,1\}$, the unbounded-error communication complexity of $f$ equals the logarithm of the sign-rank of its sign matrix $M=[(-1)^{f(x,y)}]_{x\in X,\,y\in Y}$ up to an additive constant:

$$\mathrm{UPP}(f) = \log_2 \mathrm{rk}_\pm(M) \pm O(1).$$

## Proof sketch

Lower bound: in a private-coin protocol of cost $c$, the probability of reaching a leaf $\ell$ on $(x, y)$ factors as $a_\ell(x)\, b_\ell(y)$, so $M'_{xy} = \Pr[\text{output } 0] - \Pr[\text{output } 1] = \sum_\ell \pm a_\ell(x) b_\ell(y)$ has rank at most the number of leaves, at most $2^c$, and it sign-represents $f$ because the protocol is correct with probability above $1/2$. Upper bound: take a sign representation $M'_{xy} = \langle u_x, v_y\rangle$ in $\mathbb{R}^r$ with rational entries (possible since the sign-rank is attained by integer matrices). Fix a simplex with vertices $w_0, \dots, w_r$ whose interior contains the origin, scale each $u_x$ by a positive factor so that it lies in the simplex, and write it as a convex combination $\sum_j \lambda_{x,j} w_j$. Alice sends $j$ with probability $\lambda_{x,j}$, one of $r + 1$ messages. Bob outputs $0$ with probability $\frac12\big(1 + \langle w_j, v_y\rangle / K\big)$, where $K > \max_{j,y} |\langle w_j, v_y\rangle|$, and announces it in one bit. Then $\Pr[0] - \Pr[1]$ is a positive multiple of $\langle u_x, v_y\rangle$, so the answer is correct with probability above $1/2$; all probabilities are rational, so finitely many private random bits suffice. Derived here from this count: $\lceil \log_2 \mathrm{rk}_\pm(M) \rceil \le \mathrm{UPP}(f) \le \lfloor \log_2 \mathrm{rk}_\pm(M) \rfloor + 2$, since $\lceil \log_2(r+1) \rceil \le \lfloor \log_2 r \rfloor + 1$.

## Depends on

- [Sign-rank of a Boolean matrix](sign-rank-of-a-boolean-matrix.md)
- [Unbounded-error communication complexity](unbounded-error-communication-complexity.md)

## Sources

- R. Paturi and J. Simon, "Probabilistic Communication Complexity", Journal of Computer and System Sciences 33(1), 1986.
- A. A. Sherstov, "The Unbounded-Error Communication Complexity of Symmetric Functions", Combinatorica 31(5), 2011 (Theorem 2.4, quoting Paturi and Simon, Theorem 2).
- N. Alon, S. Moran and A. Yehudayoff, "Sign Rank versus VC Dimension", COLT 2016.
