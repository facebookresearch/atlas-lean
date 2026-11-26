# Learners computed by small circuits, with adaptive or non-adaptive membership queries

A membership-query learner on $n$ coordinates has a (non-adaptive) circuit of size $S$ with $q$ queries if, for every seed, it queries $q$ points fixed by the seed and computes its hypothesis value $h(x)$ from the $q$ answers and $x$ by a fan-in-two De Morgan circuit with at most $S$ gates. It has an adaptive circuit of size $S$ with $q$ queries if, for every seed, the $i$-th query point is computed from the first $i-1$ answers by a De Morgan circuit and the hypothesis value at $x$ from all answers and $x$, with at most $S$ gates in total. A non-adaptive learner with a circuit of size $S$ is, on every seed, an oracle circuit with at most $S + q + 2$ gates, $q$ of them oracle gates at oracle depth one.

## Depends on

- [Randomized membership-query learner as a family of decision trees](membership-query-learner.md)
- [Boolean gates](../boolean-circuits/boolean-gate.md)

## Sources

- Lijie Chen, Shuichi Hirahara, Igor Carboni Oliveira, Ján Pich, Ninad Rajgopal and Rahul Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", 11th Innovations in Theoretical Computer Science Conference (ITCS 2020), 2020.
- Igor Carboni Oliveira and Rahul Santhanam, "Conspiracies Between Learning Algorithms, Circuit Lower Bounds, and Pseudorandomness", 32nd Computational Complexity Conference (CCC 2017), LIPIcs 79, 2017.
