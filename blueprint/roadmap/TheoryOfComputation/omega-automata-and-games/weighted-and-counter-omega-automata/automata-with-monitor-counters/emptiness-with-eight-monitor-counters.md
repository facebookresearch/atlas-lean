# Emptiness of deterministic sup- and limsup-automata with 8 monitor counters is undecidable

No algorithm decides, given a deterministic automaton with eight monitor counters whose value function is $\sup$, or one whose value function is $\limsup$, and a rational threshold, whether some infinite word has value at most the threshold.

**Theorem.** The emptiness problem is undecidable for deterministic $\sup$-[automata with monitor counters](automata-with-monitor-counters.md) with $8$ monitor counters, and likewise for deterministic $\limsup$-automata with $8$ monitor counters.

This completes the classification of emptiness for deterministic automata with monitor counters: it coincides with the decidability results for deterministic nested weighted automata with sum-valued slave automata, among which the $\sup$ and $\limsup$ cases are undecidable.

## Depends on

- [Automata with monitor counters](automata-with-monitor-counters.md)
- [Decidability by multi-stack machines](../../../computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof shows undecidability of emptiness for deterministic nested weighted automata with $\limsup$ (respectively $\sup$) master and sum-valued slaves of width $8$, and then applies the translation to automata with monitor counters. It reduces the halting problem for deterministic two-counter machines. Over the alphabet $Q \cup \{1, 2, \#, \natural\}$, a configuration in state $q$ with counter values $x, y$ is written $q 1^x 2^y$, configurations are separated by $\#$ and computations by $\natural$ (a dollar sign in the source). The automaton returns $0$ on words in which, from some point on, the $\natural$-separated blocks encode valid accepting computations, and a value at least $1$ otherwise. A finite-state check verifies the transitions under the abstraction of counters to zero and positive, that each computation starts in $q_I 1^0 2^0$ and ends in $q_f 1^0 2^0$, and that there are infinitely many computations. Eight slave automata (four for the transitions between even and odd positions and four for the others, two per counter of the machine) check the counter values: for a step $q 1^x 2^y \# q' 1^{x'} 2^{y'}$ that should increment counter $1$, one slave computes $-x + x' + 1$ and another $x - x' - 1$, so the larger of the two is $|x - (x' + 1)|$, which is $0$ exactly when the step is correct. The supremum, respectively limit supremum, of the slave values is therefore $0$ exactly when (eventually) all encoded computations are valid and accepting, which is possible only if the machine has an accepting computation.

## Sources

- K. Chatterjee, T. A. Henzinger and J. Otop, "Quantitative Automata under Probabilistic Semantics", *Logical Methods in Computer Science* 15(3):16, 2019, doi:10.23638/LMCS-15(3:16)2019, <https://lmcs.episciences.org/4512>; numbering of arXiv:1604.06764v4: Theorem 5.1 with its proof in Section 5, and Table 1 (known results for nested weighted automata).
