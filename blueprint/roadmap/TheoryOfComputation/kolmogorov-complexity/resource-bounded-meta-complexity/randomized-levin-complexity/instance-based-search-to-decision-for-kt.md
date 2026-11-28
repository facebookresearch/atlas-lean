# Instance-based search-to-decision reductions for Kt and rKt

From a value $k\ge\mathrm{Kt}(x)$, or one oracle query asking for a linear approximation of $\mathrm{Kt}(x)$, a randomized polynomial-time algorithm finds a Kt description of $x$ of complexity $O(k)$; the same holds for rKt. Only the input $x$ itself is ever queried.

1. There is a randomized polynomial-time algorithm that, given $x\in\{0,1\}^n$ and $k\ge\mathrm{rKt}(x)$, outputs with probability at least $0.99$ a valid rKt representation of $x$ of complexity $O(k)$.
2. There is a randomized polynomial-time algorithm that, given $x\in\{0,1\}^n$ and $k\ge\mathrm{Kt}(x)$, outputs with probability at least $0.99$ a valid Kt representation of $x$ of complexity $O(k)$.

Say a function $O:\{0,1\}^*\to\mathbb{N}$ linearly approximates rKt if $\mathrm{rKt}(x)/\gamma\le O(x)\le\gamma\cdot\mathrm{rKt}(x)$ for a constant $\gamma$. Given such an oracle, a randomized polynomial-time algorithm outputs with probability at least $0.99$ an rKt representation of $x$ of complexity $O(\mathrm{rKt}(x))$, making the single query $q=x$; the analogous statement holds for Kt. Consequently, in polynomial time one can output at most $\log n+O(1)$ strings, one of which is an rKt encoding of $x$ of complexity $O(\mathrm{rKt}(x))$, and likewise for Kt.

## Expansion

For rKt, the universal sampler run with budget $Ck$ outputs $x$ with probability at least $(2/3)2^{-Ck}/(Ck)$ in time $2^{O(Ck)}$, so the efficient coding theorem produces an encoding of complexity $O(k)$. For Kt the encoder picks a random seed $u$ of length $O(k+\log n)$, uses the deterministic isolation algorithm to obtain a hash function $H$ with $O(k)$ output bits, and outputs $(n,k,u,H(x))$; the decoder enumerates all strings of Kt complexity at most $Ck$ in time $2^{O(k)}$ and keeps the one with the right hash. Trying every power of two as $k$ gives the short list. Since the search is easy, the intractability of estimating rKt lies in checking whether a representation is valid.

## Depends on

- [Randomized Levin complexity rKt and the problem MrKtP](randomized-levin-complexity-rkt.md)
- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Proof depends on

- [Efficient coding theorem for rKt](efficient-coding-theorem-for-rkt.md)

## Sources

- Zhenjian Lu and Igor C. Oliveira, "An Efficient Coding Theorem via Probabilistic Representations and Its Applications", *48th International Colloquium on Automata, Languages, and Programming (ICALP 2021)*, LIPIcs 198, 2021, [doi:10.4230/LIPIcs.ICALP.2021.94](https://doi.org/10.4230/LIPIcs.ICALP.2021.94) (Theorem 2, Corollary 3, Definition 22, Theorems 23 and 24, Corollary 26).
