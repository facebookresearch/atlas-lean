# Language compression and conditional coding for pnK^t

Unlike deterministic time-bounded measures, $\mathrm{pnK}^t$ satisfies unconditional optimal language compression, every member of $A_n$ has complexity about $\log|A_n|$ given oracle access to $A_n$, and an unconditional conditional coding theorem for polynomial-time samplable distributions.

**Language compression.** There is a polynomial $p_{LC}$ such that for every family $A=\{A_n\subseteq\{0,1\}^n\}_{n\in\mathbb{N}}$, all $n$ and all $x\in A_n$,

$$
\mathrm{pnK}^{p_{LC}(n),A_n}(x)\le\log|A_n|+\log p_{LC}(n),
$$

where the superscript $A_n$ gives the programs oracle access to $A_n$.

**Conditional coding.** For every polynomial-time samplable family $\{D_n\}$ supported over $\{0,1\}^n\times\{0,1\}^n$ there is a polynomial $p$ such that for all $n$ and all $(x,y)$ in the support of $D_n$,

$$
\mathrm{pnK}^{p(n)}(x\mid y)\le\log\frac{1}{D_n(x\mid y)}+\log p(n).
$$

**Contrast.** Nondeterminism matters: if average-case language compression for $\mathrm{pK}$ holds for every set in P (for some $c$, $\Pr_{x\sim A_n}[\mathrm{pK}^{n^c}(x)\le\log|A_n|+c\log n]\ge 1/n^c$), then Unary-NP $\subseteq$ BPP. Conditional coding fails for $\mathrm{pK}^t$ if $\mathrm{NP}\not\subseteq\mathrm{BPP}$.

## Expansion

For language compression take $k=\lceil\log|A_n|\rceil+2$ and a pairwise-independent hash $h:\{0,1\}^n\to\{0,1\}^k$ chosen by the random string; with probability at least $3/4$ no other member of $A_n$ collides with $x$. The program stores $h(x)$, guesses $x'$, and outputs it iff $x'\in A_n$ (one oracle query) and $h(x')=h(x)$. For conditional coding with $E=D_n(x\mid y)$, the strings of conditional probability at least $E/16$ form a set $B$ of size at most $16/E$; a hash of length $\lceil\log(1/E)\rceil+7$ isolates $x$ inside $B$, and a further nondeterministically verified construction excludes guessed strings outside $B$.

## Depends on

- [Probabilistic nondeterministic time-bounded complexity pnK^t](probabilistic-nondeterministic-complexity-pnkt.md)
- [Samplable distributions](../../../pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/samplable.md)

## Proof depends on

None.

## Sources

- Jinqiao Hu, Zhenjian Lu and Igor C. Oliveira, "Hardness of Computing Nondeterministic Kolmogorov Complexity", *41st Computational Complexity Conference (CCC 2026)*, LIPIcs, 2026, [doi:10.4230/LIPIcs.CCC.2026.9](https://doi.org/10.4230/LIPIcs.CCC.2026.9) (Theorems 4, 5 and 6 and their proofs in Section 3).
