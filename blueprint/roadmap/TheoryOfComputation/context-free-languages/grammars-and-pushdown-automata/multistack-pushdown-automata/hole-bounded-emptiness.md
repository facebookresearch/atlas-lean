# Decidability of K-hole-bounded emptiness for MPDA, with witness generation

For every MPDA with finitely many states, letters and stack symbols and every $K\ge0$, it is decidable whether some word has an accepting run whose transition sequence is $K$-hole-bounded. The decision procedure explores abstract configurations consisting of a control state and a list of at most $K$ holes, each recorded by its stack and boundary states, using well-nested reachability between them (operations 'add a hole' and 'pop into a hole'); it answers 'non-empty' iff an accepting abstract configuration with no holes is reachable. Moreover, whenever the answer is 'non-empty', an explicit $K$-hole-bounded accepting run is computable by unfolding the search and the well-nested reachability derivations.

## Proof sketch

The abstract configurations form a finite graph. Soundness: each abstract step is realized by a concrete run segment that keeps the hole count. Completeness: a $K$-hole-bounded run is decomposed at hole openings and closings into well-nested factors and single pushes/pops, each mirrored by an abstract step.

## Depends on

- [Holes and hole-bounded sequences](hole-bounded-sequences.md)

## Proof depends on

- [Inductive saturation characterizes well-nested reachability](well-nested-reachability-saturation.md)
- [One hole is no hole: complete 1-hole-bounded runs are well-nested](one-hole-is-no-hole.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020, Theorem 1, Algorithm 1 and the witness-generation algorithms of Section 3.
