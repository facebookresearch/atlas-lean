# Probabilistic nondeterministic time-bounded complexity pnK^t

$\mathrm{pnK}^t_\lambda(x\mid y)$ is the least $s$ such that, with probability at least $\lambda$ over a uniformly random string $r$, the nondeterministic complexity $\mathrm{nK}^t(x\mid y;r)$ is at most $s$. It extends probabilistic time-bounded complexity $\mathrm{pK}^t$ by replacing deterministic decoding with nondeterministic decoding.

For strings $x,y$, $\lambda\in[0,1]$ and $t\in\mathbb{N}$,

$$
\mathrm{pnK}^t_\lambda(x\mid y)=\min\Bigl\{s\in\mathbb{N} : \Pr_{r\sim\{0,1\}^t}\bigl[\mathrm{nK}^t(x\mid y;r)\le s\bigr]\ge\lambda\Bigr\}.
$$

Equivalently, $\mathrm{pnK}^t_\lambda(x\mid y)\le s$ iff with probability at least $\lambda$ over $r\in\{0,1\}^t$ there is a program $\Pi$ of length at most $s$ such that every witness $w\in\{0,1\}^t$ makes $\Pi(y;w;r)$ output $x$ or $\bot$ within $t$ steps and some witness makes it output $x$. The program may depend on $r$. One writes $\mathrm{pnK}^t_\lambda(x)=\mathrm{pnK}^t_\lambda(x\mid\varepsilon)$ and omits $\lambda$ when $\lambda=2/3$.

The related randomized measure $\mathrm{rnK}^t_\lambda(x\mid y)$ uses one program $\Pi$ for all $r$: it is the least $|\Pi|$ such that, with probability at least $\lambda$ over $r$, $\Pi(y;\cdot;r)$ nondeterministically outputs $x$ in time $t$ in the above sense.

## Expansion

The order of quantifiers is the point: in $\mathrm{pnK}$ the short program is chosen after the random string, as in $\mathrm{pK}^t$, while in $\mathrm{rnK}$ it is chosen first, as in $\mathrm{rK}^t$. Allowing $\Pi$ to depend on $r$ makes hashing arguments work with nondeterministic verification, which yields the language compression, coding and symmetry-of-information properties of this measure.

## Depends on

- [Nondeterministic time-bounded Kolmogorov complexity nK^t](nondeterministic-time-bounded-complexity.md)
- [Probabilistic time-bounded Kolmogorov complexity pK^t and its conditional form](../../probabilistic-kolmogorov-and-symmetry-of-information/pkt-probabilistic-time-bounded-kolmogorov-complexity.md)

## Proof depends on

None.

## Sources

- Jinqiao Hu, Zhenjian Lu and Igor C. Oliveira, "Hardness of Computing Nondeterministic Kolmogorov Complexity", *41st Computational Complexity Conference (CCC 2026)*, LIPIcs, 2026, [doi:10.4230/LIPIcs.CCC.2026.9](https://doi.org/10.4230/LIPIcs.CCC.2026.9) (Definitions 14, 16 and 17).
