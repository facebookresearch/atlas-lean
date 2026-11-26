# Guruswami–Lyu–Wang: NC0_2-Avoid is solvable in polynomial time

There is a deterministic polynomial-time algorithm that, given $C\colon\{0,1\}^n\to\{0,1\}^m$ with $m>n$ in which every output bit depends on at most $2$ input bits, outputs $y\in\{0,1\}^m\setminus\mathrm{Im}(C)$. In addition, for any class of circuits all of whose outputs have small correlation with low-degree parities, every almost pairwise independent set contains a string avoiding the range of every circuit in the class; this gives non-trivial small hitting sets for range avoidance of $\mathrm{NC}^0$ circuits, small-width CNF and DNF, and general De Morgan formulas (the latter through approximate degree).

## Proof sketch

For a fixed target $y$, the condition $C(x)=y$ is a conjunction of constraints on pairs of variables, that is a 2-CNF, so whether $y$ is in the range is decidable in polynomial time. The algorithm fixes the bits of $y$ one at a time, maintaining the invariant that the remaining choices still contain a non-image, which is tested through 2-SAT and counting arguments on the dependency structure using $m>n$.

## Depends on

- [The range avoidance problem Avoid and its restriction C-Avoid to a circuit class](range-avoidance-problem.md)

## Sources

- Venkatesan Guruswami, Xin Lyu and Xiuhan Wang, "Range Avoidance for Low-Depth Circuits and Connections to Pseudorandomness", APPROX/RANDOM (2022), ECCC TR22-102.
