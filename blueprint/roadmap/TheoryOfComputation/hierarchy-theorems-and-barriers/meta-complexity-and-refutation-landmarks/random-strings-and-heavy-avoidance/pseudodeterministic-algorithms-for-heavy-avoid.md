# Unconditional pseudodeterministic algorithms for Heavy Avoid

For uniform implicit samplers and for polynomial-time samplers with polylogarithmic randomness, Heavy Avoid with threshold $1/(\log N)^k$ has polynomial-time pseudodeterministic algorithms that succeed on infinitely many lengths; for general polynomial-time samplers and threshold $1/N^k$, time $2^{N^{\varepsilon}}$ suffices.

Let $\mathcal{D}=\{D_N\}_{N\ge 1}$ with $D_N$ supported on $\{0,1\}^N$. A nice class of Boolean circuits contains $\mathsf{AC}^0[\oplus]$, is closed under composition and has universal circuits; $\mathsf{BP}\text{-}\mathcal{C}$ denotes DLOGTIME-uniform probabilistic $\mathcal{C}$-circuits.

1. Let $\mathcal{C}$ be nice and suppose $\mathcal{D}$ has implicit DLOGTIME-uniform $\mathcal{C}$-samplers of size $\mathrm{polylog}(N)$. For every $\delta(N)=1/(\log N)^k$, $k\in\mathbb{N}$, either $(\mathcal{D},\delta)$-Heavy-Avoid is solvable in logarithmic space on infinitely many lengths, or it is solvable pseudodeterministically by DLOGTIME-uniform $\mathsf{BP}\text{-}\mathcal{C}$ circuits of size $\mathrm{polylog}(N)$ on all lengths, each circuit outputting the $i$-th bit of the solution. For general Boolean circuits this gives a polynomial-time pseudodeterministic algorithm that succeeds on infinitely many lengths.
2. If $\mathcal{D}$ has a polynomial-time sampler of randomness complexity $(\log N)^{O(1)}$, then for every $\delta(N)=1/(\log N)^k$ there is a polynomial-time pseudodeterministic algorithm for $(\mathcal{D},\delta)$-Heavy-Avoid that succeeds on infinitely many lengths.
3. If $\mathcal{D}$ has a polynomial-time sampler, then for every $\delta(N)=1/N^k$ and every constant $\varepsilon>0$ there is a pseudodeterministic algorithm for $(\mathcal{D},\delta)$-Heavy-Avoid running in time $2^{N^{\varepsilon}}$ that succeeds on infinitely many lengths.

In all items the algorithm behaves pseudodeterministically on every input.

## Expansion

Item 1 rests on an equivalence between uniform lower bounds and deterministic Heavy Avoid algorithms: a sampler that interprets its seed as a short machine description and randomness makes every truth table of a language computed by small uniform randomized $\mathcal{C}$-circuits heavy. If $\mathsf{PSPACE}$ escapes these circuits, the separation yields logspace solvers; otherwise an extremely efficient instance checker for a special $\mathsf{PSPACE}$-complete problem lets the small randomized circuits compute a canonical light string. Items 2 and 3 instead use randomized time-bounded Kolmogorov complexity $\mathrm{rK}^t$ and its source coding theorem: heavy strings of samplers with little randomness have small $\mathrm{rK}^t$, so a canonical string of high complexity is light.

## Depends on

- [Heavy element avoidance problem](heavy-element-avoidance-problem.md)
- [Pseudodeterministic algorithms for search problems (Gat–Goldwasser)](../../../randomized-and-quantum-complexity/bounded-error-probabilistic-classes-rp-and-bpp/pseudodeterministic-algorithms/pseudodeterministic-algorithm-for-search-problem.md)

## Proof depends on

- [Time-bounded Kolmogorov complexity K^t and Levin's Kt](../../../kolmogorov-complexity/time-bounded-kolmogorov-complexity/time-bounded-kolmogorov-complexity-and-levin-kt.md)

## Sources

- Zhenjian Lu, Igor C. Oliveira, Hanlin Ren and Rahul Santhanam, "On the Complexity of Avoiding Heavy Elements", *65th IEEE Symposium on Foundations of Computer Science (FOCS 2024)*, 2024, https://doi.org/10.1109/FOCS61266.2024.00140 (Theorem II.4, Theorem II.1 and its proof sketch, Section III).
