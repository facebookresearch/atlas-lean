# One hole is no hole: complete 1-hole-bounded runs are well-nested

For every MPDA and every run from a state with all stacks empty to a state with all stacks empty, the label sequence of the run is $1$-hole-bounded if and only if it is well-nested.

## Proof sketch

Well-nested sequences have no hole pushes at all. Conversely, in a complete run every push is eventually matched; consider the first hole push $p$, whose matching pop $q$ is preceded by an unmatched crossing push of another hole push $p'$ pending at $q$. At the position just before $q$, the pushes $p$ and $p'$ belong to different open holes (they are separated by a factor that is not well-nested or use different stacks), giving two open holes and contradicting $1$-hole-boundedness.

## Depends on

- [Holes and hole-bounded sequences](hole-bounded-sequences.md)

## Sources

- S. Akshay, Paul Gastin, S. Krishna and Sparsa Roychowdhury, "Revisiting Underapproximate Reachability for Multipushdown Systems", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2020), arXiv:2002.05950, 2020, Theorem 2.
