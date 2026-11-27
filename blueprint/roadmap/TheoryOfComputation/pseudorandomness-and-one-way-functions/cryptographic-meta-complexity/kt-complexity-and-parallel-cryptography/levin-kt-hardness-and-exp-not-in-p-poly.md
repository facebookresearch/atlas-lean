# Ren–Santhanam: mild non-uniform hardness of Levin's Kt is equivalent to EXP not in P/poly

In a non-uniform regime, Levin's $\mathrm{Kt}$ captures complexity-theoretic pseudorandomness: $\mathsf{EXP}\not\subseteq\mathsf{P/poly}$ holds iff, for every $\delta>1/2$, no polynomial-size circuits compute $\mathrm{Kt}$ on a $1-2^{-\delta n}$ fraction of inputs.

A family $G_n:\{0,1\}^{\ell(n)}\to\{0,1\}^{n}$ is a *time-$t$ PRG with seed length $\ell$ against size $s$* if $G(z)$ is computable in time $t(|z|)$ and $G_n(U_{\ell(n)})$ is $1/s(n)$-indistinguishable from $U_n$ by circuits of size $s(n)$; it is *seed-extending* if $z$ is a prefix of $G(z)$. The following are equivalent:

1. $\mathsf{EXP}\not\subseteq\mathsf{P/poly}$.
2. For each $\epsilon>0$ there is a time-$2^{\ell}\mathrm{poly}(\ell)$ PRG with seed length $n^{\epsilon}$ against polynomial size.
3. There are no polynomial-size circuits for $\mathrm{Kt}$.
4. For each $\epsilon>0$ there is a seed-extending time-$2^{\ell}\mathrm{poly}(\ell)$ PRG with seed length $n^{\epsilon}$ against polynomial size.
5. For every constant $\delta>1/2$, there are no polynomial-size circuits computing $\mathrm{Kt}$ on a $1-2^{-\delta n}$ fraction of inputs of length $n$.

Thus the average-case complexity of the single problem $\mathrm{Kt}$ characterizes cryptographic pseudorandomness (against uniform adversaries with inverse-polynomial error) and complexity-theoretic pseudorandomness (against circuits with exponentially small error).

## Expansion

(1) iff (3) is the EXP-hardness of $\mathrm{Kt}$ under polynomial-size reductions (Allender et al.), and (1) iff (2) is Nisan–Wigderson. (3) implies (4): a decision version of $\mathrm{Kt}$ is computable in time $2^{n}\mathrm{poly}(n)$, so its hardness feeds the Nisan–Wigderson construction, which yields seed-extending generators. (4) implies (5): take a seed-extending generator with seed length $\gamma n$, $1-\delta<\gamma<1/2$; its outputs have $\mathrm{Kt}$ at most $2\gamma n+O(\log n)<n-\log n$, while all but an $o(1)$ fraction of uniform strings have $\mathrm{Kt}>n-\log n$. Circuits correct on a $1-2^{-\delta n}$ fraction are correct on at least $2/3$ of generator outputs, so thresholding their output at $n-\log n$ is a polynomial-size distinguisher. (5) implies (3) is trivial.

## Depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)
- [Pseudorandom generators against circuits](../../derandomization/pseudorandom-generators-against-circuits.md)

## Proof depends on

- [Nisan–Wigderson generator](../../derandomization/nisanwigderson-generator.md)

## Sources

- Hanlin Ren and Rahul Santhanam, "Hardness of KT Characterizes Parallel Cryptography", *36th Computational Complexity Conference (CCC 2021)*, LIPIcs, 2021, https://doi.org/10.4230/LIPIcs.CCC.2021.35 (Theorem 5, Definition 81, Theorems 82 and 83, Section 7.2).
