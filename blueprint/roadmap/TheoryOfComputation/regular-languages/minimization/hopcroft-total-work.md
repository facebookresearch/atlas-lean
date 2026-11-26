# Hopcroft's total-work bound

Let $M$ be a deterministic finite automaton with finite state set $Q$, $n = |Q|$, a finite enumerated alphabet $\Sigma$, transition function $\delta$ and accepting states $F$ (membership decidable). For $C \subseteq Q$ and $a \in \Sigma$, the preimage of $C$ under $a$ is $\delta_a^{-1}(C) = \{q \in Q : \delta(q, a) \in C\}$.

Hopcroft's minimization loop starts from the partition consisting of the nonempty blocks among $F$ and $Q \setminus F$, and from the waiting list of splitters $(S, b)$ for all $b \in \Sigma$, where $S$ is the smaller of $F$ and $Q \setminus F$ (with $F$ chosen on a tie); the waiting list is empty if $F$ or $Q \setminus F$ is empty. Each iteration pops the first splitter $(C, a)$ and performs Hopcroft's refinement round. Run the loop for at most $|\Sigma|(n + 1)$ iterations and let $(C_1, a_1), \dots, (C_r, a_r)$ be the splitters popped. Its predecessor cost is

$$\mathrm{cost}(M) = \sum_{i=1}^{r} \bigl( \lvert \delta_{a_i}^{-1}(C_i) \rvert + 1 \bigr).$$

The following holds: there is a constant $C \in \mathbb{N}$ such that for every such automaton,

$$\mathrm{cost}(M) \le C \, \lvert \Sigma \rvert \, (n + 1) \, \bigl( \lfloor \log_2 (n + 1) \rfloor + 1 \bigr).$$

## Sources

- J. E. Hopcroft, "An $n \log n$ algorithm for minimizing states in a finite automaton", *Theory of Machines and Computations*, 1971.
- J. Berstel, L. Boasson, O. Carton, and I. Fagnot, "Minimization of automata", 2010.
