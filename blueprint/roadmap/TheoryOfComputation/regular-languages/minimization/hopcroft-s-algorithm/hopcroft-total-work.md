# Hopcroft's total-work bound

There is a natural number $C$ such that, for every deterministic finite automaton $M$ with a finite input alphabet $\Sigma$, listed in a fixed order, a finite state set $Q$ with decidable equality and $n = |Q|$, and a decidable accepting set, the [predecessor cost](hopcroft-cost.md) of the [splitter trace](hopcroft-splitters.md) of Hopcroft's loop with fuel $|\Sigma|(n + 1)$ from the [initial partition](init-p.md) and the [initial waiting list](init-w.md) is at most

$$C\,|\Sigma|\,(n + 1)\,(\lfloor \log_2 (n + 1) \rfloor + 1).$$

The constant $C$ is absolute: it depends neither on $M$ nor on $\Sigma$. The [predecessor-work bound for the complete Hopcroft run](hopcroft-cost-complete-le.md) gives this statement with $C = 2$.

## Sources

- J. E. Hopcroft, "An $n \log n$ algorithm for minimizing states in a finite automaton", in *Theory of Machines and Computations*, Academic Press, 1971, 189–196.
- J. Berstel, L. Boasson, O. Carton and I. Fagnot, "Minimization of automata", 2010, arXiv:1010.5318 (the counting argument).
