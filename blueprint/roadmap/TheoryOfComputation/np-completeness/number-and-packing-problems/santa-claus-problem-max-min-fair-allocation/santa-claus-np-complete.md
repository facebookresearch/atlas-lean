# SANTA CLAUS (MAX-MIN FAIR ALLOCATION) is NP-complete

The SANTA CLAUS (MAX-MIN FAIR ALLOCATION) decision problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to it.

Instance: a set of `k ≥ 1` agents, a set of `m` indivisible goods, an additive valuation `vᵢ(j) ∈ ℤ₀⁺` of each good `j` for each agent `i`, and a bound `T ∈ ℤ₀⁺`. Question: is there an allocation of the goods to the agents (each good to exactly one agent) under which every agent `i` receives goods of total value `∑_{j allocated to i} vᵢ(j) ≥ T`?

## Sources

- I. Bezáková and V. Dani, "Allocating indivisible goods", ACM SIGecom Exchanges 5(3) (2005), 11-18, doi:10.1145/1120680.1120683 (the Max-Min Fairness problem).
- B. L. Deuermeyer, D. K. Friesen and M. A. Langston, "Scheduling to maximize the minimum processor finish time in a multiprocessor system", SIAM Journal on Algebraic and Discrete Methods 3 (1982), 190-196, doi:10.1137/0603019 (NP-hardness when all agents value the goods alike).
