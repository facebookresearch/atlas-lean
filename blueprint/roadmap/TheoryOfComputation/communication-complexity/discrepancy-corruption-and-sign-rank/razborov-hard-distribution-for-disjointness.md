# Razborov's hard distribution for disjointness is corrupted

Let $\ell = \lfloor n/4 \rfloor$. Let $\mu_0$ be the uniform distribution on pairs $(x, y)$ of $\ell$-subsets of $[n]$ with $x \cap y = \emptyset$, let $\mu_1$ be uniform on pairs of $\ell$-subsets with $|x \cap y| = 1$, and let $\mu = \frac34 \mu_0 + \frac14 \mu_1$. Razborov's main lemma: there are absolute constants $\alpha > 0$ and $\delta > 0$ such that for every rectangle $R = A \times B$,

$$\mu_1(R) \ge \alpha\, \mu_0(R) - 2^{-\delta n}.$$

Equivalently, under $\mu$ disjointness is $(\alpha/3,\ 2^{-\delta n}/4)$-corrupted on the answer "disjoint": every rectangle with substantial mass on disjoint pairs has a constant fraction of that mass on intersecting pairs. With the corruption bound, every deterministic protocol with sufficiently small constant error under $\mu$ has cost $\Omega(n)$; after amplification this gives the linear lower bound on $R_{1/3}$ recorded at [Randomized communication complexity of disjointness](../randomized-communication-protocols/rand-complexity-disj-fn-ge.md).

## Proof sketch

Take $n = 4m - 1$. Generate inputs by a uniformly random partition $(T_x, T_y, \{i\})$ of $[n]$ into sets of sizes $2m - 1$, $2m - 1$ and $1$, and independent uniform $m$-subsets $x \subseteq T_x \cup \{i\}$, $y \subseteq T_y \cup \{i\}$; conditioning on $i \notin x, i \notin y$ gives $\mu_0$ and on $i \in x, i \in y$ gives $\mu_1$. For a rectangle $A \times B$ and a fixed partition, $x$ and $y$ are independent, so both probabilities factor into an $A$-part and a $B$-part; a sampling argument shows that for most partitions adding $i$ to both sets does not drop either factor by more than a constant unless the rectangle is exponentially small.

## Depends on

- [Set intersection function](../randomized-communication-protocols/disj-fn.md)
- [The corruption (rectangle) bound](the-corruption-bound.md)

## Sources

- A. A. Razborov, "On the Distributional Complexity of Disjointness", Theoretical Computer Science 106(2), 1992 (the measure $\mu$, the Main Lemma, and the coupled generation with $n = 4m - 1$).
- B. Kalyanasundaram and G. Schnitger, "The Probabilistic Communication Complexity of Set Intersection", SIAM Journal on Discrete Mathematics 5(4), 1992.
- E. Kushilevitz and N. Nisan, "Communication Complexity", Cambridge University Press, 1997.
