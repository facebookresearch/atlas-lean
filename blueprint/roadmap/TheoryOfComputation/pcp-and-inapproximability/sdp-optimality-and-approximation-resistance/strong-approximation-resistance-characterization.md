# Khot–Tulsiani–Worah characterization of strong approximation resistance

Assume the Unique Games Conjecture. A predicate $P \subseteq \{-1,1\}^k$ is **strongly approximation resistant** (no efficient algorithm can find an assignment whose value deviates from $\rho(P)$ by more than $\varepsilon$ in either direction on almost-satisfiable instances) if and only if there is no ``vanishing'' measure on the polytope of first and second moments of distributions supported on $P$: precisely, $P$ is strongly approximation resistant iff for every probability measure $\Lambda$ on the moment vectors $(\mathbb{E}x_i, \mathbb{E}x_ix_j)$ of distributions on $P$, some symmetric polynomial combination of the Fourier coefficients $\hat{P}(S)$ with $\Lambda$ fails to vanish identically. This criterion is decidable for each fixed $k$.

## Proof sketch

The ``if'' direction constructs a dictatorship test from a measure on moment vectors via the invariance principle as in Raghavendra's theorem. The ``only if'' direction designs an SDP-based rounding algorithm whose advantage is a polynomial in the moment vectors; if no vanishing measure exists, a minimax argument produces a rounding scheme with nonzero bias on every almost-satisfiable instance.

## Depends on

- [Approximation-resistant predicates and balanced pairwise independence](approximation-resistance.md)

## Proof depends on

- [Raghavendra's theorem: the basic SDP is UGC-optimal for every CSP](raghavendra-optimality.md)

## Sources

- S. Khot, M. Tulsiani, P. Worah, "A characterization of strong approximation resistance", STOC (2014), arXiv:1305.5500.
