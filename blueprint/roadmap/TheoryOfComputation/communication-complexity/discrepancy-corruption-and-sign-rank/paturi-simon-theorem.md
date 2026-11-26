# Paturi–Simon: unbounded-error complexity equals log sign-rank

For every Boolean $f$ on finite sets,

$$\lceil \log_2 \mathrm{rk}_\pm(f) \rceil \le \mathrm{UPP}(f) \le \lfloor \log_2 \mathrm{rk}_\pm(f) \rfloor + 2.$$

## Proof sketch

Lower bound: for a private-coin protocol with $L$ leaves, the signed vote matrix $\sum_{s,t} (\pm 1)$ over random strings decomposes as a sum over leaves of products of an Alice-factor and a Bob-factor, so it has rank at most $L$, and it sign-represents $f$ when the error is below $1/2$. Upper bound: from a representation $\langle u_x, v_y\rangle$ in dimension $r$, Alice samples a coordinate with probability proportional to $|u_{x,i}|$ and sends it; Bob answers with a biased coin depending on $v_{y,i}$.

## Depends on

- [Sign-rank of a Boolean matrix](sign-rank-of-a-boolean-matrix.md)
- [Unbounded-error communication complexity](unbounded-error-communication-complexity.md)

## Sources

- R. Paturi and J. Simon, "Probabilistic Communication Complexity", Journal of Computer and System Sciences 33(1), 1986.
- N. Alon, S. Moran and A. Yehudayoff, "Sign Rank versus VC Dimension", COLT 2016.
