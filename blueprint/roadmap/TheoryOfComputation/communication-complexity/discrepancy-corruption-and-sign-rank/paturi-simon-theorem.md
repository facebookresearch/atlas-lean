# Paturi–Simon: unbounded-error complexity equals log sign-rank

For every Boolean $f$ on finite sets,

$$\lceil \log_2 \mathrm{rk}_\pm(f) \rceil \le \mathrm{UPP}(f) \le \lfloor \log_2 \mathrm{rk}_\pm(f) \rfloor + 2.$$

## Proof sketch

Lower bound: in a private-coin protocol of cost $c$, the probability of reaching a leaf $\ell$ on $(x, y)$ factors as $a_\ell(x)\, b_\ell(y)$, so $M_{xy} = \Pr[\text{output } 0] - \Pr[\text{output } 1] = \sum_\ell \pm a_\ell(x) b_\ell(y)$ has rank at most the number of leaves, at most $2^c$, and it sign-represents $f$ because the protocol is correct with probability above $1/2$. Upper bound: take a sign representation $M_{xy} = \langle u_x, v_y\rangle$ in $\mathbb{R}^r$ with rational entries (possible since the sign-rank is attained by integer matrices). Sampling a coordinate $i$ with probability proportional to $|u_{x,i}|$ and sending only $i$ loses the sign of $u_{x,i}$ (for $r = 1$ the rows $u = +1, -1$ would send the same message), so instead fix a simplex with vertices $w_0, \dots, w_r$ whose interior contains the origin, scale each $u_x$ by a positive factor so that it lies in the simplex, and write it as a convex combination $\sum_j \lambda_{x,j} w_j$. Alice sends $j$ with probability $\lambda_{x,j}$, one of $r + 1$ messages, in $\lceil \log_2(r+1) \rceil \le \lfloor \log_2 r \rfloor + 1$ bits. Bob outputs $0$ with probability $\frac12\big(1 + \langle w_j, v_y\rangle / K\big)$, where $K > \max_{j,y} |\langle w_j, v_y\rangle|$, and announces it in one bit. Then $\Pr[0] - \Pr[1]$ is a positive multiple of $\langle u_x, v_y\rangle$, so the answer is correct with probability above $1/2$; all probabilities are rational, so finitely many private random bits suffice.

## Depends on

- [Sign-rank of a Boolean matrix](sign-rank-of-a-boolean-matrix.md)
- [Unbounded-error communication complexity](unbounded-error-communication-complexity.md)

## Sources

- R. Paturi and J. Simon, "Probabilistic Communication Complexity", Journal of Computer and System Sciences 33(1), 1986.
- N. Alon, S. Moran and A. Yehudayoff, "Sign Rank versus VC Dimension", COLT 2016.
