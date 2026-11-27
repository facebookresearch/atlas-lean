# Programs over a monoid and bounded-width branching programs

Let $M$ be a monoid. A **program over $M$** for inputs $x\in\Sigma^{n}$ is a finite sequence of instructions $(i_k,\varphi_k)$ with $i_k\in[n]$ and $\varphi_k:\Sigma\to M$; on input $x$ it evaluates to $\prod_k\varphi_k(x_{i_k})$ (first instruction leftmost); for each fixed input $x$, evaluation is a monoid homomorphism from programs under concatenation to $M$. Width-$w$ branching programs are programs over the monoid of self-maps of $[w]$, and permutation branching programs are programs over the symmetric group $S_w$. A program over a group $G$ **$\sigma$-computes** $f:\Sigma^n\to\{0,1\}$ if it evaluates to $\sigma$ when $f(x)=1$ and to the identity when $f(x)=0$.

## Depends on

- [Deterministic and nondeterministic branching programs](branching-programs.md)

## Sources

- David A. Mix Barrington and Denis Thérien, "Finite Monoids and the Fine Structure of NC^1", Journal of the ACM 35(4), 1988.
- David A. Barrington, "Bounded-width polynomial-size branching programs recognize exactly those languages in NC^1", Journal of Computer and System Sciences 38(1), 1989.
