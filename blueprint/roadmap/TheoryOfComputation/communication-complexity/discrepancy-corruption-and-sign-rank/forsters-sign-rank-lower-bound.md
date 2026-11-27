# Forster's sign-rank lower bound

For every $X \times Y$ sign matrix $S$,

$$\mathrm{rk}_\pm(S) \ge \frac{\sqrt{|X|\,|Y|}}{\|S\|},$$

where $\|S\|$ is the spectral norm. More generally, if $M$ has no zero entries and $\mathrm{sign}(M) = S$, then $\mathrm{rk}_\pm(S) \ge \frac{\sqrt{|X||Y|}}{\|M\|} \min_{x,y}|M_{xy}|$. For the inner product modulo two on $n$ bits this gives $\mathrm{rk}_\pm \ge 2^{n/2}$, hence $\mathrm{UPP}(\mathrm{IP}_n) \ge n/2$.

## Proof sketch

Take a representation $S_{xy} = \mathrm{sign}\langle u_x, v_y\rangle$ in dimension $r$ with unit vectors, transformed so that $\sum_x u_x u_x^{\mathsf T} = \frac{|X|}{r} I$ (Forster's radial isotropic position, which exists after a small perturbation putting the $u_x$ in general position without changing any sign), with the $v_y$ also normalized to unit length. Then for each $y$, $\sum_x |\langle u_x, v_y\rangle| \ge \sum_x \langle u_x, v_y\rangle^2 = |X|/r$, so $\sum_{x,y} S_{xy}\langle u_x, v_y\rangle \ge |X||Y|/r$; on the other hand this sum is $\sum_i U_i^{\mathsf T} S V_i \le \|S\| \sqrt{|X||Y|}$ by Cauchy–Schwarz over the coordinates $i$.

## Depends on

- [Sign-rank of a Boolean matrix](sign-rank-of-a-boolean-matrix.md)

## Proof depends on

- [Paturi–Simon: unbounded-error complexity equals log sign-rank](paturi-simon-theorem.md)

## Sources

- J. Forster, "A Linear Lower Bound on the Unbounded Error Probabilistic Communication Complexity", Journal of Computer and System Sciences 65(4), 2002.
- J. Forster, M. Krause, S. V. Lokam, R. Mubarakzjanov, N. Schmitt and H. U. Simon, "Relations Between Communication Complexity, Linear Arrangements, and Computational Complexity", FSTTCS 2001 (the generalization to matrices $M$ with $\mathrm{sign}(M) = S$).
